import OAI.ThreeFlat.Profile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace OAI
namespace ThreeFlat

/-- The substitution `u = √(1/t - 1)` expresses the profile using the arctangent. -/
theorem profile_eq_atan_tail {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    profile t = 1 / 2 - (Real.arctan (Real.sqrt (1 / t - 1)) +
      Real.sqrt (1 / t - 1) / (1 + (Real.sqrt (1 / t - 1)) ^ 2)) / Real.pi := by
  let u := Real.sqrt (1 / t - 1)
  have h : 0 ≤ 1 / t - 1 := sub_nonneg.mpr ((one_le_div ht).mpr ht1)
  have hd : 1 + u ^ 2 = 1 / t := by
    dsimp only [u]
    rw [Real.sq_sqrt h]
    ring
  have hangle : Real.arctan u = Real.pi / 2 - Real.arcsin (Real.sqrt t) := by
    rw [Real.arctan_eq_arccos (Real.sqrt_nonneg _), hd, one_div, Real.sqrt_inv,
      inv_inv, Real.arccos_eq_pi_div_two_sub_arcsin]
  have hterm : u / (1 + u ^ 2) = Real.sqrt (t * (1 - t)) := by
    rw [hd, div_div_eq_mul_div, div_one]
    calc
      u * t = Real.sqrt (t ^ 2) * u := by rw [Real.sqrt_sq ht.le, mul_comm]
      _ = Real.sqrt (t ^ 2 * (1 / t - 1)) := (Real.sqrt_mul (sq_nonneg t) _).symm
      _ = _ := by
        congr 1
        field_simp [ht.ne']
  change profile t = 1 / 2 - (Real.arctan u + u / (1 + u ^ 2)) / Real.pi
  rw [hangle, hterm, profile]
  field_simp [Real.pi_ne_zero]
  ring

end ThreeFlat

end OAI
