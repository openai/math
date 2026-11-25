import OAI.LinearAlgebra.SpectralBooks.Fermion.Fermion
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Subexponential corrections to the fermionic state count

Removing the empty state changes the logarithm of a count of at least two by
at most one bit. The logarithm of the cubic overhead in a quadratic energy
cutoff is sublinear in the scaling parameter.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Filter Real
open scoped Topology

/-- Removing the empty state preserves the positive exponential growth rate. -/
theorem tendsto_label_log_of_states {H : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (h : Tendsto (fun n : ℕ ↦ logb 2 ((states (H n)).card) / n) atTop (𝓝 t)) :
    Tendsto (fun n : ℕ ↦ logb 2 (Fintype.card (Label (H n))) / n) atTop (𝓝 t) := by
  have hcount : ∀ᶠ n : ℕ in atTop, 2 ≤ (states (H n)).card := by
    filter_upwards [h.eventually (eventually_gt_nhds ht)] with n hn
    by_contra! hsmall
    interval_cases (states (H n)).card <;> simp at hn
  have hbounds : ∀ᶠ n : ℕ in atTop,
      logb 2 (states (H n)).card - 1 ≤ logb 2 (Fintype.card (Label (H n))) ∧
      logb 2 (Fintype.card (Label (H n))) ≤ logb 2 (states (H n)).card := by
    filter_upwards [hcount] with n hn
    rw [card_label]
    have hc : (2 : ℝ) ≤ (states (H n)).card := by exact_mod_cast hn
    have hp : (0 : ℝ) < (states (H n)).card - 1 := by linarith
    rw [Nat.cast_sub (by omega : 1 ≤ (states (H n)).card), Nat.cast_one]
    constructor
    · have hhalf := logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
          (show 0 < ((states (H n)).card : ℝ) / 2 by positivity)
          (show ((states (H n)).card : ℝ) / 2 ≤ (states (H n)).card - 1 by linarith)
      simpa [logb_div (show ((states (H n)).card : ℝ) ≠ 0 by positivity) (by norm_num : (2 : ℝ) ≠ 0),
        logb_self_eq_one] using hhalf
    · exact logb_le_logb_of_le (by norm_num) hp (by linarith)
  have hlow := h.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h
  · filter_upwards [hbounds] with n hn
    simpa only [sub_div] using div_le_div_of_nonneg_right hn.1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  · filter_upwards [hbounds] with n hn
    exact div_le_div_of_nonneg_right hn.2 (Nat.cast_nonneg n)

/-- A cubic factor in a quadratically growing cutoff has zero log growth rate. -/
theorem tendsto_logb_cube_overhead {H : ℕ → ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hH : ∀ n : ℕ, (H n : ℝ) ≤ q * (n : ℝ) ^ 2) :
    Tendsto (fun n : ℕ ↦ logb 2 ((H n + 1 : ℕ) ^ 3) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ logb 2 (n : ℝ) / n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hup := (tendsto_const_div_atTop_nhds_zero_nat (logb 2 (q + 1))).add (hlog.const_mul 2)
  have hupper := hup.const_mul 3
  simp only [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun n ↦ div_nonneg
      (logb_nonneg (by norm_num) (by exact_mod_cast (Nat.one_le_pow 3 _ (by omega) : 1 ≤ (H n + 1) ^ 3)))
      (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq' : 0 < q + 1 := by linarith
    have hm := logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (show 0 < (H n : ℝ) + 1 by positivity)
      (show (H n : ℝ) + 1 ≤ (q + 1) * (n : ℝ) ^ 2 by nlinarith [hH n])
    rw [logb_mul hq'.ne' (by positivity), logb_pow] at hm
    push_cast
    rw [logb_pow]
    push_cast at hm ⊢
    have hh := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simpa only [add_div, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3)

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
