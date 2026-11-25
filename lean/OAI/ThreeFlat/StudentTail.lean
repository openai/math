import OAI.ThreeFlat.StudentDerivative
import OAI.LinearAlgebra.SpectralBooks.StudentQuantile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace OAI
/-! # Closed form of the Student upper tail in dimension three -/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks Real

private theorem chiMean_three_coefficient : chiMean 3 / √(2 * π) = 2 / π := by
  have hpow : (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) = √2 * 2 := by
    rw [one_div, Real.inv_rpow (by norm_num), neg_div, Real.rpow_neg (by norm_num),
      inv_inv, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
      Real.rpow_add_one (by norm_num), ← Real.sqrt_eq_rpow]
  have hn3 : chiNormalizer 3 = √(2 * π) / 2 := by
    unfold chiNormalizer
    rw [Nat.cast_ofNat, hpow, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq, Real.sqrt_mul (by norm_num)]
    ring
  have hn4 : chiNormalizer 4 = 2 := by
    have hg : Real.Gamma 2 = 1 := by
      simp
    norm_num [chiNormalizer, hg, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [chiMean, hn3, show 3 + 1 = 4 by rfl, hn4]
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt (show 0 ≤ 2 * π by positivity)]

/-- The antiderivative of the normalized three-dimensional Student density.
The argument is scaled by the square root of the number of degrees of freedom. -/
theorem studentTail_three_scaled (a : ℝ) :
    studentTail 3 (√3 * a) = 1 / 2 - (arctan a + a / (1 + a ^ 2)) / π := by
  let f := fun x : ℝ ↦ studentTail 3 (√3 * x)
  let g := fun x : ℝ ↦ (arctan x + x / (1 + x ^ 2)) / π
  have hf (x : ℝ) : HasDerivAt f (-(2 / π) / (1 + x ^ 2) ^ 2) x := by
    have h := hasDerivAt_scaled_studentTail (d := 3) (by decide) x
    rw [chiMean_three_coefficient] at h
    convert h using 1
    norm_num [Real.rpow_neg (show 0 ≤ 1 + x ^ 2 by positivity), div_eq_mul_inv]
  have hg (x : ℝ) : HasDerivAt g ((2 / π) / (1 + x ^ 2) ^ 2) x := by
    have hden : 1 + x ^ 2 ≠ 0 := by positivity
    have hq := (hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_add 1) hden
    convert ((Real.hasDerivAt_arctan x).add hq).div_const π using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp
      ring
  have hz (x : ℝ) : HasDerivAt (fun t ↦ f t + g t) 0 x := by
    convert (hf x).add (hg x) using 1
    ring
  have h := is_const_of_deriv_eq_zero (fun x ↦ (hz x).differentiableAt) (fun x ↦ (hz x).deriv) a 0
  simpa [f, g, studentTail_zero (d := 3) (by decide), eq_sub_iff_add_eq] using h

end ThreeFlat

end OAI
