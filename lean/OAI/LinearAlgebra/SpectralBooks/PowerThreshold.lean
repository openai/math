import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI
/-! # Amplifying a strict gap by tensor powers

A strict real gap above one eventually leaves room for an integer rank
threshold. The same amplification removes any fixed multiplicative overhead.
-/

namespace LinearAlgebra.SpectralBooks

private theorem exists_pos_power_gt {a : ℝ} (ha : 1 < a) (C : ℝ) :
    ∃ n : ℕ, 0 < n ∧ C < a ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 C) ha
  exact ⟨n, Nat.pos_of_ne_zero fun hn0 => by
    subst n
    exact (le_max_left 1 C).not_gt (by simpa only [pow_zero] using hn),
    (le_max_right 1 C).trans_lt hn⟩

/-- Some common power of two separated positive real numbers straddles a
positive natural number, provided the lower base is at least one. -/
theorem exists_nat_between_powers {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    ∃ k r : ℕ, 0 < k ∧ 0 < r ∧ a ^ k < r ∧ (r : ℝ) < b ^ k := by
  have hapos : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨k, hk, hgap⟩ := exists_pos_power_gt ((one_lt_div hapos).2 hab) 2
  rw [div_pow, lt_div_iff₀ (pow_pos hapos k)] at hgap
  refine ⟨k, ⌊a ^ k⌋₊ + 1, hk, Nat.succ_pos _, Nat.lt_succ_floor _, ?_⟩
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le (pow_nonneg hapos.le k), one_le_pow₀ ha (n := k)]

/-- A constant multiplicative loss common to all positive powers disappears
when comparing their exponential growth rates. -/
theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * b ^ n) : a ≤ b := by
  by_contra! hba
  obtain ⟨n, hn, hgap⟩ := exists_pos_power_gt ((one_lt_div hb).2 hba) C
  rw [div_pow, lt_div_iff₀ (pow_pos hb n)] at hgap
  exact hgap.not_ge (h n hn)

end LinearAlgebra.SpectralBooks

end OAI
