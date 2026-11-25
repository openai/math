import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProbeFailedCount

namespace OAI
/-! # Native failure bits on the disjoint strip test rows -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators
noncomputable section

/-- The immutable slot chooses its source strip. In a purchase replay unused
slots are disabled by its authentic signed-path decision bit. -/
structure FailureWords where
  base : ℕ
  rowBits : ℕ
  rows : ℕ
  live : Expr
  score : Expr
  cut : ℕ
  globalBound : ℕ

def FailureWords.effective (s : FailureWords) :=
  Expr.branch .eq s.live (.lit 0) (.lit 0) s.score

def FailureWords.test (s : FailureWords) :=
  Expr.branch .lt (.lit s.cut) s.effective (.lit 1) (.lit 0)

def FailureWords.bank (s : FailureWords) : Bank := ⟨s.base,s.rowBits⟩

def FailureWords.pass (s : FailureWords) : Pass := ⟨s.base,s.rows,s.test⟩

def FailureWords.value {w : ℕ} (s : FailureWords) (m : Memory w) (i : Fin s.rows) :=
  (s.effective.eval m (i.val:Word w)).val

theorem FailureWords.exec {w : ℕ} (s : FailureWords) (m : Memory w) (fit : s.pass.Fits w) :
    (s.pass.procedure w).Exec m (s.pass.apply m) s.pass.clock := by
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact scan_exec _ _ _ m fit.1 fit.2 M pc reg pub exit rom data cfg start entry same

theorem FailureWords.read {w : ℕ} (s : FailureWords) (m : Memory w) (i : Fin s.rows)
    (fit : s.cut<2^w) : s.pass.apply m (s.base+i.val) =
    if s.cut<s.value m i then 1 else 0 := by
  have inside : s.base≤ s.base+i.val ∧ s.base+i.val<s.base+s.rows := by have := i.isLt; omega
  by_cases below : s.cut<s.value m i
  · rw [ite_eq_left below]
    change s.cut<(s.effective.eval m (i.val:Word w)).val at below
    simp only [pass,Pass.apply,image,fillSegment,inside,and_self,ite_true,Nat.cast_add,add_sub_cancel_left,
      test,Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt fit,
      Nat.cast_zero,Nat.cast_one,ite_eq_left below]
  · rw [ite_eq_right below]
    change ¬s.cut<(s.effective.eval m (i.val:Word w)).val at below
    simp only [pass,Pass.apply,image,fillSegment,inside,and_self,ite_true,Nat.cast_add,add_sub_cancel_left,
      test,Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt fit,
      Nat.cast_zero,Nat.cast_one,ite_eq_right below]

theorem FailureWords.frame {w : ℕ} (s : FailureWords) (m : Memory w) (x : ℕ)
    (out : x<s.base ∨ s.base+s.rows≤x) : s.pass.apply m x=m x := by
  rcases out with lo|hi
  · simp [pass,Pass.apply,image,fillSegment,not_le.mpr lo]
  · simp [pass,Pass.apply,image,fillSegment,not_lt.mpr hi]

/-- At integer precision Q, comparing to floor(2 epsilon Q) is exactly the
strict comparison of the quantized physical local score with 2 epsilon. -/
theorem fail_cut {ε : ℝ} (e : 0≤ε) {Q : ℕ} (pos : 0<Q) (v : ℕ) :
    ⌊2*ε*Q⌋₊ < v ↔ 2*ε<(v:ℝ)/Q := by
  have hq : (0:ℝ)<Q := by exact_mod_cast pos
  rw [lt_div_iff₀ hq]
  exact Nat.floor_lt (by positivity)

theorem FailureWords.paid {w : ℕ} (s : FailureWords) (m : Memory w) (actual : Fin s.rows→ℝ)
    {ε bound : ℝ} {Q : ℕ} (he : 0<ε) (bounded : 0≤bound) (hQ : 0<Q)
    (cut : s.cut=⌊2*ε*Q⌋₊) (global : s.globalBound=⌈4*ε*s.rows*Q⌉₊)
    (fit : s.cut<2^w) (positive : 0<w)
    (values : ∀ i,(s.value m i:ℝ)/Q≤bound)
    (approx : ∀ i,|(s.value m i:ℝ)/Q-actual i|≤ε)
    (trigger : s.globalBound≤∑ i,s.value m i) :
    let selected := Finset.univ.filter (fun i : Fin s.rows=>s.pass.apply m (s.base+i.val)≠0)
    2*ε*s.rows≤ selected.card*bound ∧ ∀ i∈selected,ε<actual i := by
  let raw := fun i : Fin s.rows=>s.value m i
  let adj : Fin s.rows→Fin 0→Fin s.rows := fun _=>Fin.elim0
  have big : 4*ε*s.rows*Q≤∑ i,(raw i:ℝ) := by
    rw [←Nat.cast_sum]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (global ▸ trigger))
  obtain ⟨count,hits⟩ := AdaptiveProbe.selected_failed_count raw actual adj (fun _ j=>Fin.elim0 j)
    he bounded hQ values approx big
  let fail := fun i : Fin s.rows=>decide (2*ε<(raw i:ℝ)/Q)
  have nz : (1:Word w)≠0 := by
    intro eqn
    have h := congrArg Fin.val eqn
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow positive.ne')] at h
    simp at h
  have eqn : Finset.univ.filter (fun i : Fin s.rows=>s.pass.apply m (s.base+i.val)≠0)=
      ProtocolConflictPack.picked fail adj := by
    ext i
    simp only [ProtocolConflictPack.picked,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [ProtocolConflictPack.chosen_iff fail adj i]
    have vacuous : ∀ j, adj i j < i → ¬ProtocolConflictPack.Chosen fail adj (adj i j) := fun j=>Fin.elim0 j
    rw [and_iff_left vacuous,s.read m i fit,cut]
    change (if _ then (1:Word w) else 0)≠0 ↔ decide (2*ε<(raw i:ℝ)/Q)=true
    rw [decide_eq_true_eq]
    have floorIff:=fail_cut he.le hQ (s.value m i)
    by_cases yes : ⌊2*ε*Q⌋₊<s.value m i
    · simp only [ite_eq_left yes]
      exact iff_of_true nz (floorIff.mp yes)
    · simp only [ite_eq_right yes]
      exact iff_of_false (fun neq=>neq rfl) (fun h=>yes (floorIff.mpr h))
  dsimp only
  rw [eqn]
  exact ⟨by simpa [fail] using count,hits⟩

end
end Hierarchy.ProtocolRAM

end OAI
