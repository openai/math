import OAI.LinearAlgebra.SpectralBooks.IntervalMoments
import OAI.LinearAlgebra.SpectralBooks.SphereProjections

/-! # Recovery of a sphere measure from even moments on hemispheres

On the negative hemisphere for a given projection, the squared projection determines
the projection by the negative square root. Its law is compactly supported, so
its moments determine its law. The scalar projections then determine the measure.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Set
open scoped RealInnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem negativeProjection_eq_of_even_moments
    (ξ η : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure ξ] [IsFiniteMeasure η] (z : E)
    (hmom : ∀ j : ℕ,
      (∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂ξ) =
      ∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂η) :
    (ξ.restrict {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}).map (fun x : Metric.sphere (0 : E) 1 ↦ ⟪(x : E), z⟫) =
    (η.restrict {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}).map (fun x : Metric.sphere (0 : E) 1 ↦ ⟪(x : E), z⟫) := by
  let p (x : Metric.sphere (0 : E) 1) := ⟪(x : E), z⟫
  let H := {x | p x ≤ 0}
  let q := fun x ↦ p x ^ 2
  have hp : Measurable p := by dsimp [p]; fun_prop
  have hH : MeasurableSet H := measurableSet_le hp measurable_const
  have hq : Measurable q := hp.pow_const 2
  have hbound (μ : Measure (Metric.sphere (0 : E) 1)) :
      ∀ᵐ s ∂μ.map q, s ∈ Icc 0 (‖z‖ ^ 2) := by
    apply (ae_map_iff hq.aemeasurable measurableSet_Icc).2
    refine ae_of_all _ fun x ↦ ⟨sq_nonneg _, ?_⟩
    have hpx : |p x| ≤ ‖z‖ := by simpa [p] using abs_real_inner_le_norm (x : E) z
    simpa only [q, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hpx 2
  have heq : (ξ.restrict H).map q = (η.restrict H).map q := by
    apply measure_eq_of_moments_of_mem_Icc (hbound _) (hbound _)
    intro j
    rw [integral_map hq.aemeasurable (by fun_prop), integral_map hq.aemeasurable (by fun_prop)]
    simpa only [q, p, H, ← pow_mul] using hmom j
  have hrecover (μ : Measure (Metric.sphere (0 : E) 1)) :
      ((μ.restrict H).map q).map (fun t : ℝ ↦ - Real.sqrt t) = (μ.restrict H).map p := by
    rw [Measure.map_map (by fun_prop) hq]
    refine Measure.map_congr ((ae_restrict_mem hH).mono fun x hx ↦ ?_)
    change -Real.sqrt (p x ^ 2) = p x
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hx, neg_neg]
  exact (hrecover ξ).symm.trans ((congrArg (Measure.map (fun t : ℝ ↦ -Real.sqrt t)) heq).trans
    (hrecover η))

/-- Even projection moments on all closed hemispheres determine a finite measure
on the sphere. -/
theorem sphereMeasure_eq_of_hemisphere_even_moments [FiniteDimensional ℝ E]
    (ξ η : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure ξ] [IsFiniteMeasure η]
    (hmom : ∀ (z v : E) (j : ℕ),
      (∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), v⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂ξ) =
      ∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), v⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂η) :
    ξ = η := by
  apply sphereMeasure_eq_of_negative_projection
  intro z
  exact negativeProjection_eq_of_even_moments ξ η z (hmom z z)

end

end SpectralBooks
end LinearAlgebra
end OAI
