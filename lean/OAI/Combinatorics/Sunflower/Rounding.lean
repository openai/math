import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Exponential bounds for coloring and word comparisons -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A uniformly random coloring with `k` colors is rainbow on a fixed `k`-set
with probability at least `3⁻ᵏ`. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hExp : Real.exp k ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp k = (Real.exp 1) ^ k := by simp
      _ ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hk).mp ((Real.pow_div_factorial_le_exp k (Nat.cast_nonneg k) k).trans hExp)
  exact_mod_cast h

/-- A positive coefficient of `log₂ N` in a uniform word comparison gives a
single natural base for every word length and alphabet. -/
theorem exists_natBase_of_logb_bound {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ k N : ℕ,
      (0 < N → ρ * Real.logb 2 N ≤ (k : ℝ) * c) → N ≤ D ^ k := by
  obtain ⟨D, hD⟩ := exists_nat_gt ((2 : ℝ) ^ (c / ρ))
  have hpos : 0 < (D : ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).trans hD
  have hD' : 0 < D := by exact_mod_cast hpos
  refine ⟨D, hD', ?_⟩
  intro k N h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  have hlog : Real.logb 2 N ≤ (c / ρ) * k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
    simpa only [mul_comm] using h hN
  have hcard := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hN)).mp hlog
  rw [Real.rpow_mul_natCast (by norm_num)] at hcard
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hD.le k
  exact_mod_cast hcard.trans hpow

end Sunflower
end Combinatorics
end OAI
