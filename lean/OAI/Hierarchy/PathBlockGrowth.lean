import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import OAI.Hierarchy.FixedWidthGrowth

namespace OAI
/-! # Choosing the degree in the path estimate with orthogonal edge forces -/

namespace Hierarchy.PathForcing

open Filter Real

/-- Number of proper blocks in the path decomposition of the chosen summand. -/
def blockCount (d : ℕ) : ℕ := 1 + Nat.log 2 d

/-- For a fixed exponent, choose a path on which the block count exceeds
the coefficient of the grouped-rank upper bound for size at most `q^K`. -/
theorem blocks_dominate {C : ℝ} (_hC : 0 ≤ C) (K d₀ : ℕ) :
    ∃ d ≥ d₀, 2 ≤ d ∧
      C * sqrt (blockCount d : ℝ) * ((K : ℝ) + 2) < (blockCount d : ℝ) := by
  let M := C * ((K : ℝ) + 2)
  obtain ⟨u,hu⟩ := exists_nat_gt (M ^ 2)
  let t := u + d₀ + 1
  have ltPow : t < 2^t := Nat.lt_two_pow_self
  have dt : d₀ ≤ t := by dsimp [t]; omega
  have pos : 0 < t := by dsimp [t]; omega
  refine ⟨2^t, dt.trans ltPow.le, by omega, ?_⟩
  have blocks : blockCount (2^t) = 1+t := by rw [blockCount, Nat.log_pow (by decide : 1 < (2 : ℕ))]
  let b := blockCount (2^t)
  have ub : u ≤ b := by dsimp only [b]; rw [blocks]; dsimp [t]; omega
  have large : M^2 < (b : ℝ) := hu.trans_le (by exact_mod_cast ub)
  have bpos : 0 < (b : ℝ) := lt_of_le_of_lt (by positivity) large
  have small : M < sqrt (b : ℝ) := Real.lt_sqrt_of_sq_lt large
  change C * sqrt (b : ℝ) * ((K : ℝ) + 2) < (b : ℝ)
  calc
    C * sqrt (b : ℝ) * ((K : ℝ) + 2) = M * sqrt (b : ℝ) := by dsimp [M]; ring
    _ < sqrt (b : ℝ) * sqrt (b : ℝ) := mul_lt_mul_of_pos_right small (Real.sqrt_pos.mpr bpos)
    _ = (b : ℝ) := Real.mul_self_sqrt bpos.le


/-- The grouped-rank bound on the actual path blocks forces superpolynomial
size along some fixed degree. The error coefficient may vary with the degree. -/
theorem block_superpolynomial {C : ℝ} (hC : 0 ≤ C) (E : ℕ → ℝ) (K d₀ : ℕ) :
    ∃ d ≥ d₀, 2 ≤ d ∧ ∀ᶠ q : ℕ in atTop, ∀ s : ℕ,
      (blockCount d : ℝ) * logb 2 (q : ℝ) ≤
        C * sqrt (blockCount d : ℝ) * logb 2 ((s : ℝ) + 2) +
          E d * sqrt (logb 2 (q : ℝ)) → q^K < s := by
  obtain ⟨d, hd, two, gap⟩ := blocks_dominate hC K d₀
  refine ⟨d, hd, two, ?_⟩
  filter_upwards [FixedWidth.eventually_absorb (E := E d) gap,
    eventually_ge_atTop (2 : ℕ)] with q separated hq
  intro s cut
  by_contra! hs
  have size := FixedWidth.log_size_le hq hs
  have upper := mul_le_mul_of_nonneg_left size
    (show 0 ≤ C * sqrt (blockCount d : ℝ) by positivity)
  apply (not_lt_of_ge cut)
  apply lt_of_le_of_lt (add_le_add upper (le_rfl : E d * sqrt (logb 2 (q : ℝ)) ≤ _))
  simpa only [mul_assoc] using separated


/-- The logarithmic site-price estimate also implies the fixed-degree
conclusion, since `log₂(2b) ≤ 2b` for a positive integer block count. -/
theorem block_log_superpolynomial {C : ℝ} (hC : 0 ≤ C) (E : ℕ → ℝ) (K d₀ : ℕ) :
    ∃ d ≥ d₀, 2 ≤ d ∧ ∀ᶠ q : ℕ in atTop, ∀ s : ℕ,
      (blockCount d : ℝ) * logb 2 (q : ℝ) ≤
        C * sqrt (logb 2 (2 * (blockCount d : ℝ))) * logb 2 ((s : ℝ) + 2) +
          E d * sqrt (logb 2 (q : ℝ)) → q^K < s := by
  obtain ⟨d, hd, two, result⟩ :=
    block_superpolynomial (C := C * sqrt 2) (by positivity) E K d₀
  refine ⟨d, hd, two, ?_⟩
  let b := blockCount d
  have bp : 0 < (b : ℝ) := by dsimp [b, blockCount]; positivity
  have upper : (2 : ℝ) * (b : ℝ) ≤ (2 : ℝ) ^ (2*b) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := 2*b)).le
  have logle := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) upper
  have logbound : logb 2 (2 * (b : ℝ)) ≤ 2 * (b : ℝ) := by
    simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using logle
  have roots := Real.sqrt_le_sqrt logbound
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at roots
  filter_upwards [result] with q large
  intro s cut
  apply large s
  apply cut.trans
  refine add_le_add ?_ le_rfl
  have hlog : 0 ≤ logb 2 ((s : ℝ)+2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) s; linarith)
  apply mul_le_mul_of_nonneg_right _ hlog
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left roots hC


end Hierarchy.PathForcing

end OAI
