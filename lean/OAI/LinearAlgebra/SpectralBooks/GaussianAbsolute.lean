import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Absolute first moment of the standard Gaussian -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Real Set

section

/-- The Gaussian normalization used for the mean width gives a segment of length two
when its endpoints are the two unit vectors on the real line. -/
theorem normalized_integral_abs_gaussianReal :
    √(2 * π) * (∫ x : ℝ, |x| ∂(gaussianReal 0 1)) = 2 := by
  have hpos : (∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2)) = 1 := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.Gamma_one] at h
    simpa only [neg_mul] using h
  have hfull : (∫ x : ℝ, |x| * exp (-(1 / 2) * x ^ 2)) = 2 := by
    have h := integral_comp_abs (f := fun x : ℝ ↦ x * exp (-(1 / 2) * x ^ 2))
    change (∫ x : ℝ, |x| * exp (-(1 / 2) * |x| ^ 2)) =
      2 * ∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2) at h
    simpa only [sq_abs, hpos, mul_one] using h
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  convert hfull using 1
  congr 1
  ext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_comm]
  congr 2
  ring

end

end SpectralBooks
end LinearAlgebra
end OAI
