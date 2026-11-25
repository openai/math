import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI
/-! # The fixed-mask advice union bound -/

namespace Hierarchy.FixedMaskAdvice

/-- Summing the failure probability over all advice strings and all choices
of four addresses per block gives a total strictly below one. -/
theorem union_lt_one {B h : ℕ} (hB : 0 < B) (hh : B ≤ 2 ^ h) :
    (2 : ℝ) ^ B * ((B : ℝ) ^ 4) ^ B * (((7 : ℝ) / 8) ^ (8 * (4 * h + 2))) ^ B < 1 := by
  have addresses : (B : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hh
  have decay : ((7 : ℝ) / 8) ^ (8 * (4 * h + 2)) ≤ (1 / 2 : ℝ) ^ (4 * h + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) _
  rw [← mul_pow, ← mul_pow]
  apply pow_lt_one₀ _ _ hB.ne'
  · positivity
  calc
    2 * (B : ℝ) ^ 4 * ((7 : ℝ) / 8) ^ (8 * (4 * h + 2))
        ≤ (2 * ((2 : ℝ) ^ h) ^ 4) * (1 / 2 : ℝ) ^ (4 * h + 2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) addresses 4) (by norm_num))
            decay (by positivity) (by positivity)
    _ = 1 / 2 := by
      rw [← pow_mul, Nat.mul_comm h 4, div_pow, one_pow, pow_add]
      field_simp
    _ < 1 := by norm_num

/-- At positive height the repetition count is at most 48 times the height. -/
theorem repetitions_le {h : ℕ} (hh : 1 ≤ h) : 8 * (4 * h + 2) ≤ 48 * h := by
  omega

end Hierarchy.FixedMaskAdvice

end OAI
