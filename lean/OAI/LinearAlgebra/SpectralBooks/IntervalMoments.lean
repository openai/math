import Mathlib.Probability.Moments.ComplexMGF

/-! # Moment determinacy for measures concentrated on a bounded interval -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Two finite measures concentrated on a bounded interval and having equal moments
in every natural degree are equal. -/
theorem measure_eq_of_moments_of_mem_Icc {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hm : ∀ n : ℕ, (∫ x, x ^ n ∂μ) = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hdom (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) :
      integrableExpSet id ξ = univ :=
    eq_univ_of_forall fun _ ↦ integrable_exp_mul_of_mem_Icc aemeasurable_id hξ
  have hhol (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) :
      AnalyticOnNhd ℂ (complexMGF id ξ) univ := by
    simpa [hdom ξ hξ] using (analyticOnNhd_complexMGF (X := id) (μ := ξ))
  have hder (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) (n : ℕ) :
      iteratedDeriv n (complexMGF id ξ) 0 = ((∫ x, x ^ n ∂ξ : ℝ) : ℂ) := by
    rw [iteratedDeriv_complexMGF (by simp [hdom ξ hξ])]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
      integral_complex_ofReal]
  apply Measure.ext_of_complexMGF_id_eq
  apply (hhol μ hμ).eq_of_eventuallyEq (hhol ν hν) (z₀ := 0)
  have hμseries := ((hhol μ hμ) 0 (mem_univ _)).hasFPowerSeriesAt
  have hνseries := ((hhol ν hν) 0 (mem_univ _)).hasFPowerSeriesAt
  simp_rw [hder μ hμ, hm] at hμseries
  simp_rw [hder ν hν] at hνseries
  filter_upwards [hμseries.eventually_hasSum_sub, hνseries.eventually_hasSum_sub] with z hz hz'
  exact hz.unique hz'

end SpectralBooks
end LinearAlgebra
end OAI
