import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Probability.UniformOn
import Mathlib.Tactic

/-! # Mean of a uniformly shifted residue digit -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MeasureTheory ProbabilityTheory

/-- Translating a uniform residue digit preserves its mean representative. -/
theorem integral_shiftedDigit {ℓ : ℕ} [NeZero ℓ] (k : ZMod ℓ) :
    (∫ x, ((k + x).val : ℝ) ∂uniformOn (Set.univ : Set (ZMod ℓ))) = ((ℓ : ℝ) - 1) / 2 := by
  rw [integral_fintype .of_finite]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton, one_div, ZMod.card,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum]
  have shift := Equiv.sum_comp (Equiv.addLeft k) (fun x : ZMod ℓ => (x.val : ℝ))
  change (ℓ : ℝ)⁻¹ * (∑ x : ZMod ℓ, ((Equiv.addLeft k x).val : ℝ)) = _
  rw [shift]
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change ((n + 1 : ℕ) : ℝ)⁻¹ * (∑ i : Fin (n + 1), (i.val : ℝ)) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ))]
    have hsum := Finset.sum_range_id_mul_two (n + 1)
    simp only [Nat.add_sub_cancel] at hsum
    have hreal : (∑ i ∈ Finset.range (n + 1), (i : ℝ)) * 2 = ((n : ℝ) + 1) * n := by
      rw [← Nat.cast_sum]
      exact_mod_cast hsum
    push_cast
    field_simp
    linarith

end FiniteFourier
end LinearAlgebra
end OAI
