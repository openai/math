import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter

/-- The strict slack in the interchange exponent absorbs every fixed logarithmic
power and multiplicative constant. -/
theorem eventually_logSlack (C : ℝ) (hC : 0 ≤ C) (k : ℕ) {β γ : ℝ} (hβγ : β < γ) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ^ k * x ^ β ≤ x ^ γ := by
  have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) (sub_pos.mpr hβγ)).const_mul_left
    (C * 2 ^ k)).bound zero_lt_one
  filter_upwards [h, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with x hx hlog hpos
  simp only [Real.rpow_natCast, Real.norm_eq_abs, one_mul] at hx
  have h₁ : 0 ≤ Real.log x := zero_le_one.trans hlog
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hx
  have h₂ : 1 + Real.log x ≤ 2 * Real.log x := by linarith
  calc
    _ ≤ C * (2 * Real.log x) ^ k * x ^ β := by gcongr
    _ = (C * 2 ^ k * Real.log x ^ k) * x ^ β := by rw [mul_pow, ← mul_assoc]
    _ ≤ x ^ (γ - β) * x ^ β := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hpos.le _)
    _ = x ^ γ := by rw [← Real.rpow_add hpos, sub_add_cancel]

/-- Round the ideal label radix up to the least power of two. The rounded value
still lies within a factor of two, including when the ideal radix equals one. -/
theorem exists_interchange_label_power (m : ℝ) (hm : 1 ≤ m) (s : ℕ) (hs : 0 < s) :
    ∃ k : ℕ, m ^ (s : ℝ)⁻¹ ≤ (2 : ℝ) ^ k ∧ m ≤ ((2 : ℝ) ^ k) ^ s ∧
      (2 : ℝ) ^ k ≤ 2 * m ^ (s : ℝ)⁻¹ ∧
      ∀ j < k, (2 : ℝ) ^ j < m ^ (s : ℝ)⁻¹ := by
  classical
  let r := m ^ (s : ℝ)⁻¹
  have hr : 1 ≤ r := Real.one_le_rpow hm (by positivity)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  have hex : ∃ n : ℕ, r ≤ (2 : ℝ) ^ n := ⟨j, hj.le⟩
  let k := Nat.find hex
  have hk : r ≤ (2 : ℝ) ^ k := Nat.find_spec hex
  have hmin : ∀ i < k, (2 : ℝ) ^ i < r := fun i hi => lt_of_not_ge (Nat.find_min hex hi)
  refine ⟨k, hk, ?_, ?_, hmin⟩
  · have h := pow_le_pow_left₀ (zero_le_one.trans hr) hk s
    have hrpow : r ^ s = m := by
      dsimp [r]
      rw [← Real.rpow_natCast, Real.rpow_inv_rpow (zero_le_one.trans hm) (by positivity)]
    rwa [hrpow] at h
  · cases hk' : k with
    | zero => simpa using (by linarith : (1 : ℝ) ≤ 2 * r)
    | succ n =>
      have hn := hmin n (by omega)
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left hn.le (by norm_num)

end NearSquareRoot
end Computability
end OAI
