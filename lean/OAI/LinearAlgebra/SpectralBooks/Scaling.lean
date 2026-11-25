import Mathlib

/-! # Logarithmic scaling of rectangular wire dimensions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology

noncomputable section

/-- The integer wire dimension at scale `N` and weight `w`. -/
def wireDimension (N : ℕ) (w : ℝ) : ℕ := ⌈(N : ℝ) ^ w⌉₊

theorem wireDimension_pos {N : ℕ} (hN : 0 < N) (w : ℝ) : 0 < wireDimension N w := by
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)

theorem wireDimension_log_ge {N : ℕ} (hN : 0 < N) (w : ℝ) :
    w * Real.logb 2 N ≤ Real.logb 2 (wireDimension N w) := by
  have h : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [← Real.logb_rpow_eq_mul_logb_of_pos h]
  exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos h w) (Nat.le_ceil _)

theorem dyadic_wireDimension_log_ge (k : ℕ) (w : ℝ) :
    (k : ℝ) * w ≤ Real.logb 2 (wireDimension (2 ^ k) w) := by
  have h := wireDimension_log_ge (N := 2 ^ k) (by positivity) w
  push_cast at h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, mul_comm] at h
  exact h

/-- For positive scales and nonnegative weights, rounding costs a factor of at most two. -/
theorem wireDimension_le {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    (wireDimension N w : ℝ) ≤ 2 * (N : ℝ) ^ w := by
  have hp : 1 ≤ (N : ℝ) ^ w := Real.one_le_rpow (by exact_mod_cast hN) hw
  unfold wireDimension
  linarith [Nat.ceil_lt_add_one (zero_le_one.trans hp)]

/-- Rounding a wire dimension up adds at most one bit for nonnegative weights. -/
theorem wireDimension_log_le {N : ℕ} (hN : 0 < N) {w : ℝ} (hw : 0 ≤ w) :
    Real.logb 2 (wireDimension N w) ≤ 1 + w * Real.logb 2 N := by
  calc
    _ ≤ Real.logb 2 (2 * (N : ℝ) ^ w) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast wireDimension_pos hN w) (wireDimension_le hN hw)
    _ = _ := by rw [Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]

/-- The normalized logarithmic dimension converges to the wire weight. -/
theorem tendsto_log_wireDimension_div {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun N : ℕ ↦ Real.logb 2 (wireDimension N w) / Real.logb 2 N) atTop (𝓝 w) := by
  have ht : Tendsto (fun N : ℕ ↦ (Real.logb 2 N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((Real.tendsto_logb_atTop (by norm_num)).comp
      tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun N : ℕ ↦ (Real.logb 2 N)⁻¹ + w) atTop (𝓝 w) by
      simpa using ht.add_const w)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hd := Real.logb_pos (b := 2) (by norm_num) (x := (N : ℝ)) (by exact_mod_cast hN)
    exact (le_div_iff₀ hd).mpr (wireDimension_log_ge (by omega) w)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hd := Real.logb_pos (b := 2) (by norm_num) (x := (N : ℝ)) (by exact_mod_cast hN)
    apply (div_le_iff₀ hd).mpr
    rw [add_mul, inv_mul_cancel₀ hd.ne']
    exact wireDimension_log_le (by omega) hw

end

end SpectralBooks
end LinearAlgebra
end OAI
