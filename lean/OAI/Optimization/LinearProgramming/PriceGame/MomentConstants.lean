import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The constants for the recursive trial in Section 5. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

/-- The threshold used to round an expert's mean gain or child score. -/
noncomputable def sigma : ℝ := 1 / 2 ^ 272
noncomputable def tau : ℝ := sigma / 8
noncomputable def eta : ℝ := sigma / 8
noncomputable def scale : ℝ := 2 / sigma
def probes : ℕ := 2 ^ 600 + 1

theorem sigma_pos : 0 < sigma := by norm_num [sigma]
theorem tau_pos : 0 < tau := div_pos sigma_pos (by norm_num)
theorem eta_pos : 0 < eta := tau_pos
theorem scale_pos : 0 < scale := div_pos (by norm_num) sigma_pos
private theorem pow_add_one_pos (a n : ℕ) : 0 < a ^ n + 1 := Nat.succ_pos _

theorem probes_pos : 0 < probes := pow_add_one_pos 2 600
theorem probes_odd : Odd probes := by
  refine ⟨2 ^ 599, ?_⟩
  change 2 ^ 600 + 1 = 2 * 2 ^ 599 + 1
  rw [show 600 = 599 + 1 from rfl, pow_succ, Nat.mul_comm (2 ^ 599) 2]

private theorem pow272 : (2 : ℝ) ^ 272 = 2 ^ 136 * 2 ^ 136 := pow_add 2 136 136
private theorem pow325 : (2 : ℝ) ^ 325 = 2 ^ 162 * 2 ^ 163 := pow_add 2 162 163
private theorem pow277 : (2 : ℝ) ^ (277 : ℝ) = (2 : ℝ) ^ 138 * 2 ^ 139 :=
  (Real.rpow_natCast _ 277).trans (pow_add 2 138 139)

theorem sigma_eq_trial_constants :
    sigma = (1 / 16 : ℝ) / (32 * (8 * (1 / 16 : ℝ) ^ (-(64 + 1) : ℤ))) := by
  norm_num [sigma, pow272]

/-- At either exponent used in the trial, the tail paid for rounding is absorbed by
the exponential moment at the parent. -/
theorem trialBranch_of_large {K : ℝ} (hK : 2 ^ 325 ≤ K) :
    scale ≤ K ∧ 1 + 2 * (2 : ℝ) ^ (-K * sigma / 4) ≤ 2 ^ tau := by
  constructor
  · exact le_trans (by norm_num [scale, sigma, pow325, pow272]) hK
  have hprod : (2 : ℝ) ^ 325 * sigma / 4 ≤ K * sigma / 4 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK sigma_pos.le) (by norm_num)
  have hexp : -K * sigma / 4 ≤ -(277 : ℝ) := by
    have hsmall : (277 : ℝ) ≤ 2 ^ 325 * sigma / 4 := by
      norm_num [sigma, pow325, pow272]
    rw [neg_mul, neg_div]
    exact neg_le_neg (hsmall.trans hprod)
  have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have htail : 2 * (2 : ℝ) ^ (-(277 : ℝ)) = tau / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), pow277]
    norm_num [tau, sigma, pow272]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact le_trans (by norm_num) (Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2))
  have hlogmul := mul_le_mul_of_nonneg_right hlog tau_pos.le
  calc
    1 + 2 * (2 : ℝ) ^ (-K * sigma / 4)
        ≤ 1 + 2 * (2 : ℝ) ^ (-(277 : ℝ)) := by linarith only [hrpow]
    _ = 1 + tau / 2 := by rw [htail]
    _ ≤ Real.log 2 * tau + 1 := by linarith only [hlogmul]
    _ ≤ Real.exp (Real.log 2 * tau) := Real.add_one_le_exp _
    _ = 2 ^ tau := (Real.rpow_def_of_pos (by norm_num) _).symm

private theorem probes_coe : (probes : ℝ) = (2 : ℝ) ^ 200 * 2 ^ 200 * 2 ^ 200 + 1 := by
  simp only [probes, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [show 600 = (200 + 200) + 200 from rfl, pow_add, pow_add]

theorem trialBranch_deeper :
    scale ≤ 2 * probes ∧
      1 + 2 * (2 : ℝ) ^ (-(2 * probes : ℝ) * sigma / 4) ≤ 2 ^ tau := by
  apply trialBranch_of_large
  rw [probes_coe]
  norm_num [pow325]

theorem trialBranch_local :
    scale ≤ eta * probes / Real.log 2 ∧
      1 + 2 * (2 : ℝ) ^ (-(eta * probes / Real.log 2) * sigma / 4) ≤ 2 ^ tau := by
  apply trialBranch_of_large
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  have hlog : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    (2 : ℝ) ^ 325 * Real.log 2 ≤ 2 ^ 325 * 1 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ eta * probes := by
      rw [probes_coe]
      norm_num [eta, sigma, pow325, pow272]

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
