import OAI.LinearAlgebra.SpectralBooks.ChiRadius
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The radius of a standard Gaussian vector

Cartesian factorization yields the Gaussian volume density. Polar integration then gives
the distribution of the length of the vector.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

section

private theorem pi_gaussianReal_density (q : ℕ) :
    (Measure.pi fun _ : Fin q ↦ gaussianReal 0 1) =
      volume.withDensity (fun x : Fin q → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  have hi := Integrable.fintype_prod (μ := fun i : Fin q ↦ volume.restrict (s i))
    (f := fun _ ↦ gaussianPDFReal 0 1) (fun _ ↦ (integrable_gaussianPDFReal 0 1).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall (fun x ↦
    Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ (x i)))),
    integral_fintype_prod_eq_prod (fun _ : Fin q ↦ gaussianPDFReal 0 1),
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]

private theorem prod_gaussianPDFReal (q : ℕ) (x : Fin q → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ q * Real.exp (-‖WithLp.toLp 2 x‖ ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, Finset.sum_neg_distrib]

/-- The density of a standard Gaussian vector depends only on its Euclidean norm. -/
theorem euclidean_stdGaussian_density (q : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin q)) = volume.withDensity
      (fun x : EuclideanSpace ℝ (Fin q) ↦ ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ q * Real.exp (-‖x‖ ^ 2 / 2))) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_density]
  ext s hs
  have hm := PiLp.volume_preserving_toLp (Fin q)
  rw [Measure.map_apply hm.measurable hs, withDensity_apply _ (hm.measurable hs),
    withDensity_apply _ hs]
  simp_rw [prod_gaussianPDFReal]
  exact hm.setLIntegral_comp_preimage hs (f := fun x : EuclideanSpace ℝ (Fin q) ↦
    ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ q * Real.exp (-‖x‖ ^ 2 / 2))) (by fun_prop)

/-- Polar integration reduces an arbitrary radial observable to one real integral. -/
theorem integral_stdGaussian_norm {q : ℕ} (hq : 0 < q) (f : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin q), f ‖x‖ ∂stdGaussian _ =
      ((q : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1) *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ q) *
        ∫ r in Ioi (0 : ℝ), r ^ (q - 1) * Real.exp (-r ^ 2 / 2) * f r := by
  let _ : NeZero q := ⟨hq.ne'⟩
  rw [euclidean_stdGaussian_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ q := by positivity
  simp only [ENNReal.toReal_ofReal (mul_nonneg hc (Real.exp_pos _).le), smul_eq_mul]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin q)))
    (fun r ↦ ((Real.sqrt (2 * Real.pi))⁻¹ ^ q * Real.exp (-r ^ 2 / 2)) * f r)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc (q : ℝ), mul_assoc ((q : ℝ) * _)]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  ring

/-- Integrating the norm of a standard Gaussian vector against its chi density. -/
theorem integral_stdGaussian_norm_eq_chi {q : ℕ} (hq : 0 < q) (f : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin q), f ‖x‖ ∂stdGaussian _ =
      ∫ r, chiDensity q r * f r := by
  have h := integral_stdGaussian_norm hq (fun _ ↦ 1)
  rw [integral_chiKernel_nat_eq hq] at h
  simp only [integral_const, probReal_univ, one_smul, mul_one,
    integral_chiDensity hq] at h
  rw [integral_stdGaussian_norm hq, integral_chiKernel_nat_eq hq, ← mul_assoc, ← h, one_mul]

/-- Orthonormal coordinates give the same radial integral on an arbitrary Euclidean space. -/
theorem integral_stdGaussian_norm_eq_chi_finrank (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hq : 0 < Module.finrank ℝ E) (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E = ∫ r, chiDensity (Module.finrank ℝ E) r * f r := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have hm : MeasurePreserving e (stdGaussian E) (stdGaussian _) :=
    ⟨e.continuous.measurable, stdGaussian_map e⟩
  rw [← integral_stdGaussian_norm_eq_chi hq,
    ← hm.integral_comp e.toHomeomorph.measurableEmbedding (fun x ↦ f ‖x‖)]
  simp

/-- The length of a standard Gaussian vector in positive dimension has the chi law. -/
theorem map_norm_stdGaussian_eq_chi {q : ℕ} (hq : 0 < q) :
    (stdGaussian (EuclideanSpace ℝ (Fin q))).map (fun x ↦ ‖x‖) =
      volume.withDensity (fun r ↦ ENNReal.ofReal (chiDensity q r)) := by
  have := isFiniteMeasure_withDensity_ofReal (integrable_chiDensity hq).2
  ext s hs
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [← integral_indicator_one hs, ← integral_indicator_one hs,
    integral_map (by fun_prop) ((measurable_one.indicator hs).aestronglyMeasurable),
    integral_stdGaussian_norm_eq_chi hq, integral_withDensity_eq_integral_toReal_smul
      (measurable_chiDensity q).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (chiDensity_nonneg hq _), smul_eq_mul]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
