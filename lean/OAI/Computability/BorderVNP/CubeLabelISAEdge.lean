import OAI.Computability.BorderVNP.RoutingISANatural
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-!
# Native per-cable mean update in a label trial

The two outputs are the contributions before and after pinning the current cell,
in units of the common denominator `Z²`. Each cable has two distinct endpoints.
Register 5 is zero when the current cell is its source. Registers 3 and 4 hold
the source and destination bins. The other endpoint has been pinned precisely
when its index in register 6 is below the current index in register 1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Scaled cable mean before choosing the current label. -/
def edgeBefore (z c other otherLabel otherBin width : ℕ) : ℕ :=
  if other < c then if otherLabel = otherBin then width*z else 0 else width

/-- Pinning the current endpoint multiplies a matching contribution by the label count. -/
def edgeAfter (z v ownBin before : ℕ) : ℕ := if v = ownBin then before*z else 0

private def bins : Code :=
  .ifEq 5 11 (.seq (.copy 12 3) (.copy 13 4)) (.seq (.copy 12 4) (.copy 13 3))

private def before : Code :=
  .ifLt 6 1 (.ifEq 7 13 (.binary .mul 9 8 0) (.copy 9 11)) (.seq (.copy 9 8) .nop)

private def after : Code :=
  .ifEq 2 12 (.binary .mul 10 9 0) (.copy 10 11)

/-- Fixed table for one incident descriptor. Registers 9 and 10 receive the two
scaled means, register 11 holds zero, and registers 12 and 13 hold the oriented bins. -/
def edgeContrib : Code := .block [.constant 11 0, bins, before, after]

/-- No choice, sign change, or call occurs in the edge contribution. -/
theorem edgeContrib_deterministic : edgeContrib.deterministic = true := rfl

/-- All registers outside the two outputs and three scratch words are preserved. -/
theorem edgeContrib_keeps (k : Reg) (h : k.val < 9 ∨ 13 < k.val) :
    edgeContrib.keeps k = true := by
  have ne (d : Reg) (lo : 9 ≤ d.val) (hi : d.val ≤ 13) : k ≠ d := by
    rintro rfl
    omega
  simp [edgeContrib, Code.block, bins, before, after, Code.keeps, ne 9 (by decide) (by decide),
    ne 10 (by decide) (by decide), ne 11 (by decide) (by decide), ne 12 (by decide) (by decide),
    ne 13 (by decide) (by decide)]

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {m : Memory w}

private theorem bins_run (s : Bank w) :
    ∃ t, Runs pub macros bins s m (List.replicate 3 (tick w)) t m ∧
      t 12 = (if s 5 = s 11 then s 3 else s 4) ∧
      t 13 = (if s 5 = s 11 then s 4 else s 3) ∧
      ∀ k, k ≠ 12 → k ≠ 13 → t k = s k := by
  have branch (i j : Reg) (hj : j ≠ 12) :
      ∃ t, Runs pub macros (.seq (.copy 12 i) (.copy 13 j)) s m [tick w, tick w] t m ∧
        t 12 = s i ∧ t 13 = s j ∧ ∀ k, k ≠ 12 → k ≠ 13 → t k = s k := by
    let s' := Function.update s 12 (s i)
    have a : Runs pub macros (.copy 12 i) s m [tick w] s' m := Runs.localStep m rfl rfl
    have b : Runs pub macros (.copy 13 j) s' m [tick w] (Function.update s' 13 (s' j)) m :=
      Runs.localStep m rfl rfl
    exact ⟨_, a.seq b, by simp (config := {decide := true}) [s'], by simp [s',hj],
      fun k h₁ h₂ => by simp [s',h₁,h₂]⟩
  by_cases h : s 5 = s 11
  · obtain ⟨t,run,h₁,h₂,rest⟩ := branch 3 4 (by decide)
    exact ⟨t, Runs.ifEq (by simpa [h] using run), by simpa [h] using h₁,
      by simpa [h] using h₂, rest⟩
  · obtain ⟨t,run,h₁,h₂,rest⟩ := branch 4 3 (by decide)
    exact ⟨t, Runs.ifEq (by simpa [h] using run), by simpa [h] using h₁,
      by simpa [h] using h₂, rest⟩

private theorem before_run (s : Bank w) :
    let b := if s 6 < s 1 then (if s 7 = s 13 then s 8 * s 0 else s 11) else s 8
    Runs pub macros before s m (List.replicate 3 (tick w)) (Function.update s 9 b) m := by
  dsimp only
  apply Runs.ifLt
  by_cases h : s 6 < s 1
  · simp only [h, ite_true]
    apply Runs.ifEq
    by_cases he : s 7 = s 13 <;> simp only [he, ite_true, ite_false] <;> exact Runs.localStep m rfl rfl
  · simp only [h, ite_false]
    have a : Runs pub macros (.copy 9 8) s m [tick w] (Function.update s 9 (s 8)) m :=
      Runs.localStep m rfl rfl
    have b : Runs pub macros .nop _ m [tick w] (Function.update s 9 (s 8)) m :=
      Runs.localStep m rfl rfl
    exact a.seq b

private theorem after_run (s : Bank w) :
    let b := if s 2 = s 12 then s 9 * s 0 else s 11
    Runs pub macros after s m (List.replicate 2 (tick w)) (Function.update s 10 b) m := by
  dsimp only
  apply Runs.ifEq
  by_cases h : s 2 = s 12 <;> simp only [h, ite_true, ite_false] <;> exact Runs.localStep m rfl rfl

/-- Execute the oriented edge calculation on actual words. The scale bound ensures
that both multiplications agree with natural arithmetic. Every path takes nine
ordinary plus ticks and leaves shared memory untouched. -/
theorem edgeContrib_run (s : Bank w) (hz : 0 < (s 0).val)
    (fit : (s 8).val * (s 0).val^2 < 2^w) :
    let own := if (s 5).val = 0 then (s 3).val else (s 4).val
    let other := if (s 5).val = 0 then (s 4).val else (s 3).val
    let b := edgeBefore (s 0).val (s 1).val (s 6).val (s 7).val other (s 8).val
    ∃ t, Runs pub macros edgeContrib s m (List.replicate 9 (tick w)) t m ∧
      (t 9).val = b ∧ (t 10).val = edgeAfter (s 0).val (s 2).val own b ∧
      ∀ k : Reg, k.val < 9 ∨ 13 < k.val → t k = s k := by
  let s₀ := Function.update s 11 (0 : Word w)
  have r₀ : Runs pub macros (.constant 11 0) s m [tick w] s₀ m := Runs.localStep m rfl rfl
  obtain ⟨s₁,r₁,h₁₂,h₁₃,hrest⟩ := bins_run (pub := pub) (macros := macros) (m := m) s₀
  let b := if s₁ 6 < s₁ 1 then (if s₁ 7 = s₁ 13 then s₁ 8 * s₁ 0 else s₁ 11) else s₁ 8
  let s₂ := Function.update s₁ 9 b
  let a := if s₂ 2 = s₂ 12 then s₂ 9 * s₂ 0 else s₂ 11
  let s₃ := Function.update s₂ 10 a
  have run : Runs pub macros edgeContrib s m (List.replicate 9 (tick w)) s₃ m :=
    r₀.seq (r₁.seq ((before_run s₁).seq (after_run s₂)))
  have hr (k : Reg) (hk : k.val < 11) : s₁ k = s k := by
    have h₁ : k ≠ 11 := by rintro rfl; norm_num at hk
    have h₂ : k ≠ 12 := by rintro rfl; norm_num at hk
    have h₃ : k ≠ 13 := by rintro rfl; norm_num at hk
    simpa [s₀, h₁] using hrest k h₂ h₃
  have hzero : s₁ 11 = 0 := by simpa [s₀] using hrest 11 (by decide) (by decide)
  simp (config := {decide := true}) [s₀] at h₁₂ h₁₃
  have hmul : (s 8).val * (s 0).val < 2^w := by
    rw [pow_two, ← Nat.mul_assoc] at fit
    exact (Nat.le_mul_of_pos_right _ hz).trans_lt fit
  let own := if (s 5).val = 0 then (s 3).val else (s 4).val
  let other := if (s 5).val = 0 then (s 4).val else (s 3).val
  have orient : s 5 = 0 ↔ (s 5).val = 0 := Fin.ext_iff
  have hown : (s₁ 12).val = own := by simp only [h₁₂,apply_ite Fin.val, orient,own]
  have hother : (s₁ 13).val = other := by simp only [h₁₃,apply_ite Fin.val, orient,other]
  have hb : b.val = edgeBefore (s 0).val (s 1).val (s 6).val (s 7).val other (s 8).val := by
    simp only [b,hr 6 (by decide),hr 1 (by decide),hr 7 (by decide),hr 8 (by decide),
      hr 0 (by decide),hzero,apply_ite Fin.val,Fin.lt_def,Fin.ext_iff,Fin.val_mul,
      Nat.mod_eq_of_lt hmul,hother,edgeBefore,Fin.val_zero]
  have hb_le : b.val ≤ (s 8).val * (s 0).val := by
    rw [hb,edgeBefore]; split
    · split <;> omega
    · exact Nat.le_mul_of_pos_right _ hz
  have ha_fit : b.val * (s 0).val < 2^w := by
    rw [pow_two, ← Nat.mul_assoc] at fit
    exact (Nat.mul_le_mul_right _ hb_le).trans_lt fit
  rw [hb] at ha_fit
  refine ⟨s₃,run,?_,?_,fun k hk => run.keepsReg (edgeContrib_keeps k hk)⟩
  · change (s₃ 9).val = edgeBefore _ _ _ _ other _
    simpa (config := {decide := true}) [s₃,s₂] using hb
  · change (s₃ 10).val = edgeAfter _ _ own (edgeBefore _ _ _ _ other _)
    simp (disch := decide) only [s₃,s₂,a,Function.update_self,Function.update_of_ne,
      hr 2 (by decide),hr 0 (by decide),hzero,apply_ite Fin.val,Fin.ext_iff,Fin.val_mul,
      hown,Nat.mod_eq_of_lt ha_fit,hb,edgeAfter,Fin.val_zero]
end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
