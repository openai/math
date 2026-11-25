import OAI.ThreeFlat.Profile
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI
namespace ThreeFlat

/-- A cubic lower estimate for sine gives an all-rational certificate at `40/43`. -/
theorem oneThird_le_profile_forty_div_fortyThree : (1 : ℝ) / 3 ≤ profile (40 / 43) := by
  have hsin : (529 : ℝ) / 2000 ≤ Real.sin (67 / 250) := by
    apply le_trans _ (Real.sin_ge_sub_cube (x := 67 / 250) (by norm_num))
    norm_num
  have hcos : Real.cos (67 / 250) ≤ Real.sqrt (40 / 43) := by
    apply Real.le_sqrt_of_sq_le
    have hsquare := pow_le_pow_left₀ (by norm_num : 0 ≤ (529 : ℝ) / 2000) hsin 2
    nlinarith only [hsquare, Real.sin_sq_add_cos_sq (67 / 250)]
  have hangle : Real.pi / 2 - 67 / 250 ≤ Real.arcsin (Real.sqrt (40 / 43)) := by
    apply (Real.le_arcsin_iff_sin_le' (x := Real.pi / 2 - 67 / 250)
      ⟨by linarith [Real.pi_gt_three], by linarith⟩).2
    rwa [Real.sin_pi_div_two_sub]
  have hsqrt : Real.sqrt ((40 : ℝ) / 43 * (1 - 40 / 43)) ≤ 51 / 200 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num
  unfold profile
  apply (le_div_iff₀ Real.pi_pos).2
  linarith [Real.pi_gt_d2]

/-- The rational lower bound `43/20` for the three-flat square exponent constant. -/
theorem fortyThree_div_twenty_le_omegaThree : (43 : ℝ) / 20 ≤ omegaThree := by
  calc
    (43 : ℝ) / 20 = 2 / (40 / 43 : ℝ) := by norm_num
    _ ≤ omegaThree := omegaThree_ge_of_profile ⟨by norm_num, by norm_num⟩
      oneThird_le_profile_forty_div_fortyThree

end ThreeFlat

end OAI
