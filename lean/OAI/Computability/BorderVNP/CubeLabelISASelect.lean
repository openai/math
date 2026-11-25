import OAI.Computability.BorderVNP.CubeFirstMinimum
import OAI.Computability.BorderVNP.RoutingISANatural
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Native least-minimizer scan of the label trials

The first candidate initializes the incumbent. Subsequent candidates replace it
only on strict score improvement, so ties are resolved by the public label order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private def saveBest : Code := .seq (.copy 17 2) (.copy 18 16)

private def compareBest : Code := .ifLt 16 18 saveBest .nop

private def selectBody (candidate : Code) : Code :=
  .seq candidate (.seq compareBest (.binary .add 2 2 20))

/-- Fixed label scan. Register 0 holds the positive alphabet size, 20 holds one,
and 23 holds zero. A candidate fragment receives its label in 2 and returns its
score in 16. The final least minimizing label and score are left in 17 and 18. -/
def select (candidate : Code) : Code :=
  .block [.copy 2 23, candidate, saveBest, .copy 2 20, .whileLt 2 0 (selectBody candidate)]

/-- The selection instructions introduce writes only to the label cursor and
the two incumbent registers. -/
theorem select_keeps {candidate : Code} {r : Reg} (h : candidate.keeps r = true)
    (h₂ : r ≠ 2) (h₁₇ : r ≠ 17) (h₁₈ : r ≠ 18) : (select candidate).keeps r = true := by
  simp [select,Code.block,selectBody,compareBest,saveBest,Code.keeps,h,h₂,h₁₇,h₁₈]

/-- Selection introduces no nondeterminism. -/
theorem select_deterministic {candidate : Code} (h : candidate.deterministic = true) :
    (select candidate).deterministic = true := by
  simp [select,Code.block,selectBody,compareBest,saveBest,Code.deterministic,h]

variable {w z : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {m : Memory w}
  {candidate : Code} {cost : ℕ} {f : Fin (z+1) → ℕ} {Ready : Bank w → Prop}

/-- The candidate fragment's required register and cost interface. Persistent
input registers, the label cursor, and the two incumbents survive each trial. -/
structure SelectionTrial (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (candidate : Code) (cost : ℕ) (f : Fin (z+1) → ℕ)
    (Ready : Bank w → Prop) : Prop where
  /-- The alphabet size and the constants used by the scan are present. -/
  values : ∀ s, Ready s → (s 0).val = z+1 ∧ (s 20).val = 1 ∧ (s 23).val = 0
  /-- Cursor and incumbent assignments preserve the candidate input invariant. -/
  write : ∀ s, Ready s → ∀ r : Reg, r = 2 ∨ r = 17 ∨ r = 18 →
    ∀ v, Ready (Function.update s r v)
  /-- Candidate evaluation preserves the registers owned by the minimizer. -/
  keeps : ∀ r : Reg, r = 2 ∨ r = 17 ∨ r = 18 → candidate.keeps r = true
  /-- A fitted trial returns the actual natural score in register 16. -/
  run : ∀ (i : Fin (z+1)) s, Ready s → (s 2).val = i.val →
    ∃ es t, Runs pub macros candidate s m es t m ∧ traceCost es ≤ cost ∧ Ready t ∧ (t 16).val = f i

private def Best (f : Fin (z+1) → ℕ) (k : ℕ) (b : Fin (z+1)) : Prop :=
  b.val < k ∧ ∀ j : Fin (z+1), j.val < k → f b ≤ f j ∧ (f j ≤ f b → b ≤ j)

private theorem best_next {i b : Fin (z+1)} (h : Best f i.val b) :
    Best f (i.val+1) (if f i < f b then i else b) := by
  obtain ⟨hb,hmin⟩ := h
  by_cases hlt : f i < f b
  · simp only [hlt,ite_true,Best]
    refine ⟨by omega,fun j hj => ?_⟩
    by_cases he : j = i
    · subst j; exact ⟨le_rfl,fun _ => le_rfl⟩
    · have hne : j.val ≠ i.val := fun e => he (Fin.ext e)
      have h' := (hmin j (by omega)).1
      exact ⟨by omega,fun hj' => by omega⟩
  · simp only [hlt,ite_false,Best]
    refine ⟨by omega,fun j hj => ?_⟩
    by_cases he : j = i
    · subst j; exact ⟨by omega,fun _ => Fin.le_def.mpr (by omega)⟩
    · have hne : j.val ≠ i.val := fun e => he (Fin.ext e)
      exact hmin j (by omega)

private def saved (s : Bank w) : Bank w :=
  Function.update (Function.update s 17 (s 2)) 18 (s 16)

private theorem save_run (s : Bank w) :
    Runs pub macros saveBest s m [tick w,tick w] (saved s) m := by
  let u := Function.update s 17 (s 2)
  have a : Runs pub macros (.copy 17 2) s m [tick w] u m := Runs.localStep m rfl rfl
  have b : Runs pub macros (.copy 18 16) u m [tick w] (Function.update u 18 (u 16)) m :=
    Runs.localStep m rfl rfl
  simpa (config := {decide := true}) [u,saved,saveBest] using a.seq b

private theorem saved_ready (ctx : SelectionTrial pub macros m candidate cost f Ready)
    {s : Bank w} (hr : Ready s) : Ready (saved s) :=
  ctx.write _ (ctx.write _ hr 17 (by simp) _) 18 (by simp) _

private theorem compare_run (ctx : SelectionTrial pub macros m candidate cost f Ready)
    (s : Bank w) (hr : Ready s) {b i : Fin (z+1)}
    (hb : (s 17).val = b.val) (hs : (s 18).val = f b)
    (hi : (s 2).val = i.val) (hf : (s 16).val = f i) :
    let b' := if f i < f b then i else b
    ∃ es t, Runs pub macros compareBest s m es t m ∧ traceCost es ≤ 3 ∧ Ready t ∧
      (t 17).val = b'.val ∧ (t 18).val = f b' ∧ t 2 = s 2 := by
  dsimp only
  by_cases h : f i < f b
  · have guard : s 16 < s 18 := Fin.lt_def.mpr (by simpa [hf,hs] using h)
    simp only [h,ite_true]
    refine ⟨_,saved s,Runs.ifLt (by simpa [guard] using save_run s),by rfl, saved_ready ctx hr,?_,?_,?_⟩
    all_goals simp (config := {decide := true}) [saved,hi,hf]
  · have guard : ¬ s 16 < s 18 := fun he => h (by simpa [hf,hs] using Fin.lt_def.mp he)
    have no : Runs pub macros .nop s m [tick w] s m := Runs.localStep m rfl rfl
    simp only [h,ite_false]
    exact ⟨_,s,Runs.ifLt (by simpa [guard] using no), by change 2 ≤ 3; decide, hr,hb,hs,rfl⟩

private theorem select_loop (ctx : SelectionTrial pub macros m candidate cost f Ready)
    (s : Bank w) (hr : Ready s) (hle : (s 2).val ≤ z+1) (b : Fin (z+1))
    (hb : (s 17).val = b.val) (hs : (s 18).val = f b) (best : Best f (s 2).val b) :
    ∃ es t, Runs pub macros (.whileLt 2 0 (selectBody candidate)) s m es t m ∧
      traceCost es ≤ (z+1-(s 2).val)*(cost+5)+1 ∧ Ready t ∧
      (t 17).val = (Cube.firstMinimum f).val ∧ (t 18).val = f (Cube.firstMinimum f) := by
  by_cases hlt : (s 2).val < z+1
  · let i : Fin (z+1) := ⟨_,hlt⟩
    have guard : s 2 < s 0 := Fin.lt_def.mpr ((ctx.values s hr).1.symm ▸ hlt)
    obtain ⟨es,u,ru,eu,hu,fu⟩ := ctx.run i s hr rfl
    have keep (r : Reg) (h : r = 2 ∨ r = 17 ∨ r = 18) : u r = s r :=
      ru.keepsReg (ctx.keeps r h)
    have hu₂ : (u 2).val = i.val := congrArg Fin.val (keep 2 (by simp))
    obtain ⟨fs,v,rv,ev,hv,bv,sv,hv₂⟩ := compare_run ctx u hu
      ((congrArg Fin.val (keep 17 (by simp))).trans hb)
      ((congrArg Fin.val (keep 18 (by simp))).trans hs) hu₂ fu
    let t := Function.update v 2 (v 2 + v 20)
    have rt : Runs pub macros (.binary .add 2 2 20) v m [tick w] t m := Runs.localStep m rfl rfl
    have ht : Ready t := ctx.write _ hv 2 (by simp) _
    have hfit : z+1 < 2^w := (ctx.values v hv).1 ▸ (v 0).isLt
    have hvval := (congrArg Fin.val hv₂).trans hu₂
    have ht₂ : (t 2).val = i.val+1 := by
      simp only [t,Function.update_self,Fin.val_add,(ctx.values v hv).2.1,hvval]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    let b' := if f i < f b then i else b
    have ht₁₇ : (t 17).val = b'.val := by simpa (config := {decide := true}) [t,b'] using bv
    have ht₁₈ : (t 18).val = f b' := by simpa (config := {decide := true}) [t,b'] using sv
    obtain ⟨rest,out,rr,er,ho,bo,so⟩ := select_loop ctx t ht (by rw [ht₂]; exact i.isLt) b'
      ht₁₇ ht₁₈ (ht₂.symm ▸ best_next (i := i) best)
    refine ⟨_,out,Runs.whileStep guard (ru.seq (rv.seq rt)) rr,?_,ho,bo,so⟩
    change 1 + traceCost ((es ++ (fs ++ [tick w])) ++ rest) ≤ _
    simp only [traceCost,VPVNP.RAMBuckets.cost_append]
    have hdec : z+1-(s 2).val = (z+1-(t 2).val)+1 := by dsimp [i] at ht₂; omega
    rw [hdec,Nat.add_mul,one_mul]
    change 1+(traceCost es + (traceCost fs + 1) + traceCost rest) ≤ _
    omega
  · have he : (s 2).val = z+1 := by omega
    have guard : ¬ s 2 < s 0 := fun h => hlt ((ctx.values s hr).1 ▸ Fin.lt_def.mp h)
    have hfirst : Cube.firstMinimum f = b := (Cube.firstMinimum_eq_iff f b).mpr
      ⟨fun j => (best.2 j (he.symm ▸ j.isLt)).1,fun j => (best.2 j (he.symm ▸ j.isLt)).2⟩
    exact ⟨_,s,Runs.whileDone guard,by change 1 ≤ _; omega, hr,hfirst.symm ▸ hb,hfirst.symm ▸ hs⟩
termination_by z+1-(s 2).val
decreasing_by
  change z+1-(t 2).val < z+1-(s 2).val
  dsimp only [i] at ht₂
  rw [ht₂]
  omega

/-- A genuine native traversal of all candidates returns the mathematical least
minimizer, using one call to the scoring fragment per label. -/
theorem select_run (ctx : SelectionTrial pub macros m candidate cost f Ready)
    (s : Bank w) (hr : Ready s) :
    ∃ es t, Runs pub macros (select candidate) s m es t m ∧
      traceCost es ≤ (z+1)*(cost+5)+4 ∧ Ready t ∧
      (t 17).val = (Cube.firstMinimum f).val ∧ (t 18).val = f (Cube.firstMinimum f) := by
  let u := Function.update s 2 (s 23)
  have ru : Runs pub macros (.copy 2 23) s m [tick w] u m := Runs.localStep m rfl rfl
  have hu := ctx.write s hr 2 (by simp) (s 23)
  have hu₂ : (u 2).val = (0 : Fin (z+1)).val := by simpa [u] using (ctx.values s hr).2.2
  obtain ⟨es,v,rv,ev,hv,hf⟩ := ctx.run 0 u hu hu₂
  have hv₂ : (v 2).val = (0 : Fin (z+1)).val := (congrArg Fin.val (rv.keepsReg (ctx.keeps 2 (by simp)))).trans hu₂
  let a := saved v
  have ra := save_run (pub := pub) (macros := macros) (m := m) v
  have ha : Ready a := saved_ready ctx hv
  let t := Function.update a 2 (a 20)
  have rt : Runs pub macros (.copy 2 20) a m [tick w] t m := Runs.localStep m rfl rfl
  have ht : Ready t := ctx.write a ha 2 (by simp) _
  have ht₂ : (t 2).val = 1 := by simpa [t] using (ctx.values a ha).2.1
  have best : Best f (t 2).val 0 := by
    rw [ht₂]
    refine ⟨by simp,fun j hj => ?_⟩
    have hj₀ : j = 0 := Fin.ext (by simpa using (show j.val = 0 by omega))
    subst j
    exact ⟨le_rfl,fun _ => le_rfl⟩
  obtain ⟨rest,out,ro,er,ho,bo,so⟩ := select_loop ctx t ht (by omega) 0
    (by simpa (config := {decide := true}) [t,a,saved] using hv₂)
    (by simpa (config := {decide := true}) [t,a,saved] using hf) best
  refine ⟨_,out,ru.seq (rv.seq (ra.seq (rt.seq ro))),?_,ho,bo,so⟩
  simp only [traceCost,VPVNP.RAMBuckets.cost_append]
  change 1 + (traceCost es + (2 + (1 + traceCost rest))) ≤ _
  rw [ht₂, Nat.add_sub_cancel] at er
  rw [Nat.add_mul,one_mul]
  omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
