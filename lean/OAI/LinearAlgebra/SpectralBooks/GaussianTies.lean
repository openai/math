import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Uniqueness of projections of a finite set in a Gaussian direction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A tie between two distinct points has Gaussian measure zero, since their
difference gives a one-dimensional projection of positive variance. -/
theorem measure_projection_tie_eq_zero {x y : E} (hxy : x ≠ y) :
    stdGaussian E {u : E | ⟪u, x⟫ = ⟪u, y⟫} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ (x - y)
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have : NullSingletonClass ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal]
    apply nullSingletonClass_gaussianReal
    rw [variance_dual_stdGaussian, ne_eq, Real.toNNReal_eq_zero, not_le]
    simpa only [L, innerSL_apply_norm] using sq_pos_of_pos hnorm
  have hzero := measure_singleton (μ := (stdGaussian E).map L) (0 : ℝ)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton _)] at hzero
  convert hzero using 2
  ext u
  change ⟪u, x⟫ = ⟪u, y⟫ ↔ ⟪x - y, u⟫ = 0
  rw [real_inner_comm u (x - y), inner_sub_right, sub_eq_zero]

/-- Almost every Gaussian direction separates every pair in a finite point set. -/
theorem ae_no_ties (S : Finset E) :
    ∀ᵐ u ∂stdGaussian E, ∀ x ∈ S, ∀ y ∈ S, ⟪u, x⟫ = ⟪u, y⟫ → x = y := by
  apply (ae_ball_iff S.countable_toSet).2
  intro x _
  apply (ae_ball_iff S.countable_toSet).2
  intro y _
  by_cases hxy : x = y
  · exact Filter.Eventually.of_forall fun _ _ ↦ hxy
  have h : ∀ᵐ u ∂stdGaussian E, ⟪u, x⟫ ≠ ⟪u, y⟫ := by
    simpa only [ae_iff, not_not] using measure_projection_tie_eq_zero hxy
  filter_upwards [h] with u hu heq using False.elim (hu heq)

end

end SpectralBooks
end LinearAlgebra
end OAI
