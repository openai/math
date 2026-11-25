import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Growth forced by the logarithmic load of a fixed graph

For a fixed graph the error grows as the square root of the logarithm of the
edge alphabet. A load of slope greater than `k + 1` thus rules out an ABP of
size at most `n ^ k` at every sufficiently large alphabet size `n`.
-/

namespace Hierarchy

/-- The additive two in the rank budget costs at most two binary logarithm units. -/
theorem fixedGraph_log_size_of_le_power (n k s : ℕ) (hn : 1 ≤ n) (hs : s ≤ n ^ k) :
    Real.logb 2 (s + 2 : ℕ) ≤ (k : ℝ) * Real.logb 2 n + 2 := by
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ hn'
  have hs' : (s : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast hs
  have bound : ((s + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 2 * (n : ℝ) ^ k := by
    push_cast
    nlinarith
  have hlog := Real.logb_le_logb_of_le hbase (by positivity) bound
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0) (by linarith : (n : ℝ) ^ k ≠ 0),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hbase] at hlog
  simpa only [Nat.cast_ofNat, mul_one, add_comm] using hlog

/-- For widths at least two, the additive logarithm cost can be absorbed into the exponent. -/
theorem fixedGraph_log_size_le_slope (n k s : ℕ) (hn : 2 ≤ n) (hs : s ≤ n ^ k) :
    Real.logb 2 (s + 2 : ℕ) ≤ ((k : ℝ) + 2) * Real.logb 2 n := by
  have h := fixedGraph_log_size_of_le_power n k s (by omega) hs
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw := Real.logb_le_logb_of_le hbase (show (0 : ℝ) < 2 by norm_num) hn'
  rw [Real.logb_self_eq_one hbase] at hw
  linarith

/-- An explicit dyadic threshold makes every larger alphabet have logarithm at least `C`. -/
theorem fixedGraph_log_eventually_ge (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, C ≤ Real.logb 2 n := by
  obtain ⟨m, hm⟩ := exists_nat_ge C
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  refine ⟨2 ^ m, hp, fun n hn => hm.trans ?_⟩
  have hnreal : (2 : ℝ) ^ m ≤ (n : ℝ) := by exact_mod_cast hn
  have base : (1 : ℝ) < 2 := by norm_num
  have h := Real.logb_le_logb_of_le base (by positivity) hnreal
  simpa only [Real.logb_pow, Real.logb_self_eq_one base, mul_one] using h

/-- A quadratic lower bound on the width parameter absorbs the fixed square-root error. -/
theorem fixedGraph_sqrt_error_le_half (A B w : ℝ) (hw : 0 ≤ w) (hlarge : 4 * A * B ≤ w) :
    Real.sqrt (A * w * B) ≤ w / 2 := by
  apply (Real.sqrt_le_left (show 0 ≤ w / 2 by linarith)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlarge hw]

/-- For all sufficiently large widths, the fixed-graph lower bound forces
size strictly larger than the prescribed power. -/
theorem fixedGraph_eventually_superpower (A B R : ℝ) (k : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : (k : ℝ) + 1 < R) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ,
      R * Real.logb 2 n ≤ Real.logb 2 (s + 2 : ℕ) + Real.sqrt (A * Real.logb 2 n * B) →
        n ^ k < s := by
  obtain ⟨N, hN, hlog⟩ := fixedGraph_log_eventually_ge (4 * A * B + 4)
  refine ⟨N, fun n hn s hload => ?_⟩
  let w := Real.logb 2 n
  have hwidth : 4 * A * B + 4 ≤ w := hlog n hn
  have large : 4 ≤ w := by nlinarith [mul_nonneg hA hB]
  have nonneg : 0 ≤ w := by linarith
  have coeff : 4 * A * B ≤ w := by linarith
  have error := fixedGraph_sqrt_error_le_half A B w nonneg coeff
  by_contra! hs
  have size := fixedGraph_log_size_of_le_power n k s (hN.trans hn) hs
  change Real.logb 2 (s + 2 : ℕ) ≤ (k : ℝ) * w + 2 at size
  change R * w ≤ Real.logb 2 (s + 2 : ℕ) + Real.sqrt (A * w * B) at hload
  have slope := mul_lt_mul_of_pos_right hR (show 0 < w by linarith)
  linarith

end Hierarchy

end OAI
