import OAI.LinearAlgebra.SpectralBooks.NormalTail
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # A Gaussian first moment on a half-line

The explicit first moment evaluates the expected gain when a book tip
at height `a` exceeds a fixed spine support value `h`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open ProbabilityTheory MeasureTheory Filter Set Real
open scoped Topology

/-- The first moment of a standard normal restricted to a half-line is the
normal density at its endpoint. -/
theorem normal_truncated_first_moment (s : ℝ) :
    (∫ z in Ioi s, z ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-s ^ 2 / 2) := by
  let b : ℝ := 1 / 2
  have hb : 0 < b := by norm_num [b]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ ↦ -exp (-b * y ^ 2))
      (x * exp (-b * x ^ 2)) x := by
    convert! (((hasDerivAt_pow 2 x).const_mul (-b)).exp).neg using 1
    dsimp [b]
    ring
  have ht : Tendsto (fun y : ℝ ↦ -exp (-b * y ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))).neg
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' (a := s) (fun x _ ↦ hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht
  rw [← integral_indicator measurableSet_Ioi, integral_gaussianReal_eq_integral_smul one_ne_zero]
  calc
    _ = ∫ z, (Ioi s).indicator (fun z ↦ (√(2 * π))⁻¹ * (z * exp (-b * z ^ 2))) z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Ioi s
      · simp [indicator_of_mem hz, gaussianPDFReal, smul_eq_mul, b, div_eq_mul_inv,
          mul_assoc, mul_comm, mul_left_comm]
      · simp [indicator_of_notMem hz]
    _ = (√(2 * π))⁻¹ * (∫ z in Ioi s, z * exp (-b * z ^ 2)) := by
      rw [integral_indicator measurableSet_Ioi, integral_const_mul]
    _ = _ := by
      rw [hI]
      simp [b, div_eq_mul_inv, mul_comm]

/-- For positive height the expected positive part is a truncated first
moment minus the threshold times the upper-tail mass. -/
theorem normalHinge_integral (a h : ℝ) (ha : 0 < a) :
    (∫ z, max (a * z - h) 0 ∂gaussianReal 0 1) =
      a * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(h / a) ^ 2 / 2) -
        h * normalTail (h / a) := by
  have hid : Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp)
  have hind : (fun z : ℝ ↦ max (a * z - h) 0) =
      (Ioi (h / a)).indicator (fun z ↦ a * z - h) := by
    funext z
    by_cases hz : z ∈ Ioi (h / a)
    · rw [indicator_of_mem hz, max_eq_left]
      exact sub_nonneg.mpr (by simpa [mul_comm] using ((div_lt_iff₀ ha).mp hz).le)
    · rw [indicator_of_notMem hz, max_eq_right]
      exact sub_nonpos.mpr (by simpa [mul_comm] using (le_div_iff₀ ha).mp (le_of_not_gt hz))
  rw [normalTail, hind, integral_indicator measurableSet_Ioi,
    integral_sub (hid.const_mul a).integrableOn (integrable_const h),
    integral_const_mul, normal_truncated_first_moment, setIntegral_const, smul_eq_mul]
  ring

end SpectralBooks
end LinearAlgebra
end OAI
