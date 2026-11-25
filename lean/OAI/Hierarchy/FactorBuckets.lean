import Mathlib.Data.Nat.Find
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI
/-! # Computable geometric resource classes for the diagonal schedule -/

namespace Hierarchy.FactorBucket

private def level (w x : ℕ) : ℕ :=
  Nat.findGreatest (fun i => 21^i ≤ 20^i*x) (20*(w+1))

/-- Tests use integer arithmetic, including at exact bin boundaries. Zero has
its own label and positive costs have strictly positive labels. -/
def label (w x : ℕ) : Fin (20*(w+1)+2) :=
  if x=0 then 0 else ⟨level w x+1, by
    have := Nat.findGreatest_le (P:=fun i=>21^i ≤ 20^i*x) (20*(w+1))
    unfold level
    omega⟩

theorem label_val_of_ne {w x : ℕ} (h : x ≠ 0) :
    (label w x).val = Nat.findGreatest (fun i => 21^i ≤ 20^i*x) (20*(w+1)) + 1 := by
  simp [label,level,h]

noncomputable def lower (w : ℕ) (c : Fin (20*(w+1)+2)) : ℝ :=
  if c.val=0 then 0 else (21/20:ℝ)^(c.val-1)

theorem lower_nonneg (w : ℕ) (c : Fin (20*(w+1)+2)) : 0≤lower w c := by
  unfold lower
  split <;> positivity

private theorem eligible_iff (x i : ℕ) :
    21^i ≤ 20^i*x ↔ (21/20:ℝ)^i ≤ x := by
  rw [div_pow, div_le_iff₀ (by positivity : 0<(20:ℝ)^i), mul_comm (x:ℝ)]
  exact_mod_cast Iff.rfl

private theorem ceiling (w : ℕ) : (2:ℝ)^w < (21/20:ℝ)^(20*(w+1)) := by
  rw [pow_mul]
  exact (pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) (Nat.le_succ w)).trans_lt
    (pow_lt_pow_left₀ (by norm_num : (2:ℝ)<(21/20:ℝ)^20) (by norm_num) (Nat.succ_ne_zero w))

/-- Positive entries lie between their lower endpoint and 21/20 times it.
At zero both endpoints are zero. -/
theorem bounds (w x : ℕ) (fits : x≤2^w) :
    lower w (label w x) ≤ (x:ℝ) ∧ (x:ℝ) ≤ (21/20:ℝ)*lower w (label w x) := by
  by_cases hz : x=0
  · subst x
    simp [label,lower]
  let i:=level w x
  have hit : (21/20:ℝ)^i ≤ x := (eligible_iff x i).mp
    (Nat.findGreatest_spec (P:=fun n=>21^n ≤ 20^n*x) (Nat.zero_le (20*(w+1))) (by simp;omega))
  have bound : i ≤ 20*(w+1) := Nat.findGreatest_le (P:=fun n=>21^n ≤ 20^n*x) _
  have room : i < 20*(w+1) := by
    by_contra! opp
    have eq := Nat.le_antisymm bound opp
    rw [eq] at hit
    have lim : (x:ℝ)≤(2:ℝ)^w := by exact_mod_cast fits
    exact (not_lt_of_ge (hit.trans lim)) (ceiling w)
  have miss : ¬21^(i+1) ≤ 20^(i+1)*x :=
    Nat.findGreatest_is_greatest (P:=fun n=>21^n ≤ 20^n*x)
      (show level w x < i+1 by dsimp only [i];omega) (by omega)
  have upper := lt_of_not_ge (fun h=>(miss ((eligible_iff x (i+1)).mpr h)))
  have base : lower w (label w x)=(21/20:ℝ)^i := by simp [label,lower,hz,i]
  rw [base]
  exact ⟨hit,by simpa only [pow_succ,mul_comm (21/20:ℝ)] using upper.le⟩

end Hierarchy.FactorBucket

end OAI
