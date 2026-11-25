import OAI.LinearAlgebra.SpectralBooks.StudentTail
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI
/-! # Differentiation of the Student tail after rescaling the threshold -/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

private theorem hasDerivAt_normalTail (s : ℝ) :
    HasDerivAt normalTail (-gaussianPDFReal 0 1 s) s := by
  have hc : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]
    fun_prop
  have h := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s 0)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply (h.add_const (∫ x in Ioi 0, gaussianPDFReal 0 1 x)).congr_of_eventuallyEq
  filter_upwards with t
  rw [normalTail, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1)),
    intervalIntegral.integral_interval_add_Ioi
      (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn]

/-- Differentiation of the Gaussian mixture uses its size-biased chi law,
whose squared-radius Laplace transform gives the Student density. -/
theorem hasDerivAt_scaled_studentTail {d : ℕ} (hd : 0 < d) (a : ℝ) :
    HasDerivAt (fun x : ℝ => studentTail d (√d * x))
      (-(chiMean d / √(2 * π)) * (1 + a ^ 2) ^ (-((d : ℝ) + 1) / 2)) a := by
  let k := chiMean d / √(2 * π)
  have hk : 0 ≤ k := div_nonneg (chiMean_pos hd).le (sqrt_nonneg _)
  let f := fun (x h : ℝ) => chiDensity d h * normalTail (x * h)
  let g := fun (x h : ℝ) => -k * (chiDensity (d + 1) h * exp (-(x ^ 2 * h ^ 2) / 2))
  have intg (x : ℝ) : Integrable (g x) :=
    (integrable_chiDensity_laplace (Nat.succ_pos d) (sq_nonneg x)).const_mul _
  have der (x h : ℝ) : HasDerivAt (fun u => f u h) (g x h) x := by
    have H := ((hasDerivAt_normalTail (x * h)).comp x ((hasDerivAt_id x).mul_const h)).const_mul
      (chiDensity d h)
    convert H using 1 <;> try rfl
    change -k * (chiDensity (d + 1) h * exp (-(x ^ 2 * h ^ 2) / 2)) =
      chiDensity d h * (-gaussianPDFReal 0 1 (x * h) * (1 * h))
    rw [gaussianPDFReal_def]
    simp only [k, NNReal.coe_one, mul_one, sub_zero, one_mul, mul_pow]
    linear_combination - (√(2 * π))⁻¹ * exp (-(x ^ 2 * h ^ 2) / 2) *
      (chiDensity_sizeBias hd h).symm
  have bd (x h : ℝ) : ‖g x h‖ ≤ k * chiDensity (d+1) h := by
    have hr := chiDensity_nonneg (Nat.succ_pos d) h
    have he := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg x) (sq_nonneg h))) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [g]
    rw [Real.norm_eq_abs, neg_mul, abs_neg, abs_of_nonneg (by positivity)]
    rw [← mul_assoc]
    exact mul_le_of_le_one_right (mul_nonneg hk hr) he
  have H := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := f) (F' := g) (s := Set.univ) (bound := fun h => k * chiDensity (d + 1) h)
    univ_mem (.of_forall fun x => (integrable_chiDensity_mul_normalTail hd x).aestronglyMeasurable)
    (integrable_chiDensity_mul_normalTail hd a) (intg a).aestronglyMeasurable
    (ae_of_all _ fun h x _ => bd x h) ((integrable_chiDensity (Nat.succ_pos d)).const_mul k)
    (ae_of_all _ fun h x _ => der x h)).2
  have hdn : √(d : ℝ) ≠ 0 := (sqrt_pos_of_pos (by exact_mod_cast hd)).ne'
  simpa only [f, g, k, studentTail, mul_div_cancel_left₀ _ hdn, integral_const_mul,
    integral_chiDensity_laplace (Nat.succ_pos d) (sq_nonneg a), Nat.cast_add_one] using H

end ThreeFlat

end OAI
