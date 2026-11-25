import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Conditioning of the synchronized two-coordinate phase factors -/

namespace OAI
namespace Computability
namespace NearSquareRoot

/-- The first row of the Walsh rotation of the dilation pair has unit norm.
Both entries stay uniformly away from zero, including at a zero multiplier. -/
theorem synchronizedPair_bounds (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    let t := Real.sqrt (1 - ‖z‖ ^ 2)
    let h := (Real.sqrt 2)⁻¹
    let a := (h : ℂ) * (z + t)
    let b := (h : ℂ) * (t - star z)
    (1 / 5 : ℝ) ≤ ‖a‖ ∧ (1 / 5 : ℝ) ≤ ‖b‖ ∧ ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
  let t := Real.sqrt (1 - ‖z‖ ^ 2)
  let h := (Real.sqrt 2)⁻¹
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have hz₂ : ‖z‖ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg z) hz]
  have ht₂ : t ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt (by linarith)
  have ht : 5 / 6 ≤ t := by nlinarith
  have hq : 0 < Real.sqrt 2 := by positivity
  have hq₂ := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  have hh : 2 / 3 ≤ h := by
    change 2 / 3 ≤ (Real.sqrt 2)⁻¹
    rw [← one_div, le_div_iff₀ hq]
    nlinarith
  have hh₀ : 0 ≤ h := by linarith
  have hh₂ : h ^ 2 = 1 / 2 := by
    dsimp [h]
    rw [inv_pow, hq₂, one_div]
  have hzplus : t - ‖z‖ ≤ ‖z + t‖ := by
    simpa only [Complex.norm_of_nonneg ht₀, norm_neg, sub_neg_eq_add, add_comm] using
      norm_sub_norm_le (t : ℂ) (-z)
  have hzminus : t - ‖z‖ ≤ ‖(t : ℂ) - star z‖ := by
    simpa only [Complex.norm_of_nonneg ht₀, Complex.star_def, Complex.norm_conj] using
      norm_sub_norm_le (t : ℂ) (star z)
  change 1 / 5 ≤ ‖(h : ℂ) * (z + t)‖ ∧ 1 / 5 ≤ ‖(h : ℂ) * (t - star z)‖ ∧
    ‖(h : ℂ) * (z + t)‖ ^ 2 + ‖(h : ℂ) * (t - star z)‖ ^ 2 = 1
  simp only [Complex.norm_mul, Complex.norm_of_nonneg hh₀]
  have lower {x : ℝ} (hx : t - ‖z‖ ≤ x) : 1 / 5 ≤ h * x := by
    have hx' : 1 / 3 ≤ x := by linarith
    nlinarith [mul_le_mul hh hx' (by norm_num) hh₀]
  refine ⟨lower hzplus, lower hzminus, ?_⟩
  rw [mul_pow, mul_pow, hh₂]
  have hzsq := Complex.sq_norm_sub_sq_re z
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith

end NearSquareRoot
end Computability
end OAI
