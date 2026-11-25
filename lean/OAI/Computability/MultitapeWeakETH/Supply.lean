import OAI.Computability.MultitapeWeakETH.Normalization

/-! # Supply costs and simultaneous bounds for a common graph -/

namespace OAI.Computability.MultitapeWeakETH

open Finset VPVNP.SpectralGeometry
open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

def directedMultiplicity (src dst : E → V) (i j : V) : ℕ :=
  ∑ e, if src e = i then (if dst e = j then 1 else 0) else 0

def supplyMultiplicity (src dst : E → V) (i j : V) :=
  directedMultiplicity src dst i j + directedMultiplicity dst src i j

omit [Fintype V] in
theorem supplyMultiplicity_symm (src dst : E → V) (v w : V) :
    supplyMultiplicity src dst v w = supplyMultiplicity src dst w v := by
  have flip (s t : E → V) (i j : V) : directedMultiplicity s t i j = directedMultiplicity t s j i := by
    apply sum_congr rfl
    intro e _
    by_cases hs : s e = i <;> by_cases ht : t e = j <;> simp [hs,ht]
  change _ + _ = _ + _
  rw [flip src dst v w,flip dst src v w,add_comm]

theorem supplyMultiplicity_row (src dst : E → V) (v : V) :
    ∑ w, supplyMultiplicity src dst v w =
      (univ.filter fun e => src e = v).card + (univ.filter fun e => dst e = v).card := by
  classical
  have row (s t : E → V) : ∑ w, directedMultiplicity s t v w = (univ.filter fun e => s e = v).card := by
    unfold directedMultiplicity
    rw [sum_comm]
    simp_rw [sum_ite_irrel, sum_const_zero]
    simp
  simp only [supplyMultiplicity,sum_add_distrib,row]

private theorem directedCost (src dst : E → V) (f : V → V → ℝ) :
    (∑ i, ∑ j, (directedMultiplicity src dst i j : ℝ)*f i j) = ∑ e, f (src e) (dst e) := by
  classical
  have term (i j) : (directedMultiplicity src dst i j : ℝ)*f i j =
      ∑ e, if src e = i then (if dst e = j then f i j else 0) else 0 := by
    unfold directedMultiplicity
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro e _
    by_cases hs : src e = i <;> by_cases ht : dst e = j <;> simp [hs,ht]
  simp_rw [term]
  calc
    _ = ∑ e, ∑ i, ∑ j, if src e = i then (if dst e = j then f i j else 0) else 0 := by
      rw [sum_comm (s := (univ : Finset E)) (t := (univ : Finset V))]
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := by simp [sum_ite_irrel]

theorem supply_energy_le {X : Type} [MetricSpace X] (p : V → X) (src dst : E → V)
    (H : Matrix V V ℕ) {degree : ℕ} (positive : 0 < degree)
    (contains : ∀ i j, supplyMultiplicity src dst i j ≤ H i j) :
    ∑ e, dist (p (src e)) (p (dst e))^2 ≤ degree*walkEnergy (normalizeArcs H degree) p := by
  rw [← directedCost src dst (fun v w => dist (p v) (p w)^2)]
  simp only [walkEnergy,normalizeArcs,mul_sum]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  have le : directedMultiplicity src dst i j ≤ H i j := (Nat.le_add_right _ _).trans (contains i j)
  have coe : (0:ℝ) < degree := Nat.cast_pos.mpr positive
  rw [dist_comm (p j) (p i),← mul_assoc,← mul_div_assoc,mul_div_cancel_left₀ _ coe.ne']
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast le) (sq_nonneg _)

/-- Converting a quadratic estimate into the wire cost only uses the
number of edges and the maximum bit width. -/
theorem weighted_supply_cost (w : E → ℝ) (ℓ : E → ℝ) {cap budget : ℝ}
    (weights : ∀ e, w e ≤ cap) (cap_nonneg : 0 ≤ cap) (distances : ∀ e, 0 ≤ ℓ e)
    (energy : ∑ e, (ℓ e)^2 ≤ budget) :
    ∑ e, w e*ℓ e ≤ cap * Real.sqrt (Fintype.card E) * Real.sqrt budget := by
  have cs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ : E => (1:ℝ)) ℓ
  simp at cs
  calc
    _ ≤ ∑ e, cap*ℓ e := sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (weights e) (distances e)
    _ = cap*(∑ e, ℓ e) := (mul_sum ..).symm
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ cap_nonneg
      exact cs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt energy) (Real.sqrt_nonneg _))

end OAI.Computability.MultitapeWeakETH
