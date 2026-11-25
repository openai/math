import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Finset
open scoped BigOperators

variable {ι : Type*}

/-- Back substitution in the normalized triangular pivot submatrix. If all
coordinates of the represented vector have magnitude at most one, the sum
of the coefficient magnitudes is at most `2^k - 1`. -/
theorem triangular_l1_bound (k : ℕ) (row : ℕ → ι → ℝ) (pivot : ℕ → ι)
    (c : ℕ → ℝ) (x : ι → ℝ)
    (hdiag : ∀ i < k, row i (pivot i) = 1)
    (hzero : ∀ i < k, ∀ j < k, i < j → row j (pivot i) = 0)
    (hr : ∀ i < k, ∀ j, |row i j| ≤ 1)
    (hx : ∀ j, |x j| ≤ 1)
    (hrep : ∀ j, x j = ∑ s ∈ range k, c s * row s j) :
    ∑ s ∈ range k, |c s| ≤ 2 ^ k - 1 := by
  have coeff (i : ℕ) (hi : i < k) :
      |c i| ≤ 1 + ∑ s ∈ range i, |c s| := by
    have hsplit : ∑ s ∈ range (i + 1), c s * row s (pivot i) =
        ∑ s ∈ range k, c s * row s (pivot i) := by
      apply sum_subset (range_mono hi)
      intro j hj hji
      simp only [mem_range] at hj hji
      rw [hzero i hi j hj (by omega), mul_zero]
    rw [sum_range_succ, hdiag i hi, mul_one, ← hrep] at hsplit
    have eq : c i = x (pivot i) - ∑ s ∈ range i, c s * row s (pivot i) := by linarith
    calc
      |c i| = |x (pivot i) - ∑ s ∈ range i, c s * row s (pivot i)| := congrArg abs eq
      _ ≤ |x (pivot i)| + |∑ s ∈ range i, c s * row s (pivot i)| := abs_sub _ _
      _ ≤ 1 + ∑ s ∈ range i, |c s * row s (pivot i)| :=
        add_le_add (hx _) (abs_sum_le_sum_abs _ _)
      _ ≤ _ := by
        apply add_le_add (le_refl 1)
        apply sum_le_sum
        intro s hs
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hr s (by simp only [mem_range] at hs; omega) _)
  have pref (p : ℕ) (hp : p ≤ k) : ∑ s ∈ range p, |c s| ≤ 2 ^ p - 1 := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [sum_range_succ, pow_succ]
      linarith [ih (by omega), coeff p (by omega)]
  exact pref k le_rfl

/-- The paper's dimension choice makes the rounded projection error smaller
than half the separation tolerance; all constants are retained. -/
theorem projection_precision (n : ℕ) (hn : 0 < n) :
    30 * (n : ℝ) ^ 3 * 4 ^ n * (2 : ℝ) ^ (-(100 * (n + 1) ^ 3 : ℕ) : ℝ) ≤
      1 / (2000 * (n : ℝ)) := by
  have hpow (m : ℕ) : m ≤ 2 ^ m := by
    induction m with
    | zero => decide
    | succ m ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ m := by positivity
      omega
  have hn4 : n ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left (hpow n) 4
  have hbig : 60000 * n ^ 4 * 4 ^ n ≤ 2 ^ (100 * (n + 1) ^ 3) := by
    calc
      60000 * n ^ 4 * 4 ^ n ≤ 2 ^ 16 * (2 ^ n) ^ 4 * (2 ^ 2) ^ n := by gcongr <;> norm_num
      _ = 2 ^ (16 + n * 4 + 2 * n) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hp : (0 : ℝ) < 2 ^ (100 * (n + 1) ^ 3) := by positivity
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 60000 * (n : ℝ) ^ 4 * 4 ^ n ≤ (2 : ℝ) ^ (100 * (n + 1) ^ 3) := by
    exact_mod_cast hbig
  rw [← div_eq_mul_inv, div_le_div_iff₀ hp (by positivity)]
  nlinarith only [hb]

end Geometry
end LinearProgramming
end Optimization
end OAI
