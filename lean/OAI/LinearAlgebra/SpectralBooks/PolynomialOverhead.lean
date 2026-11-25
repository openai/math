import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Removing polynomial overheads from tensor-power inequalities -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology NNReal

/-- A fixed polynomial overhead in a comparison of all positive powers
disappears at the level of exponential growth rates. -/
theorem le_of_pow_le_polynomial_mul_pow {x y : ℝ} (hy : 0 ≤ y) (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ) + 1) ^ L * y ^ m) : x ≤ y := by
  by_contra! hxy
  have hx := hy.trans_lt hxy
  have hr := tendsto_pow_const_mul_const_pow_of_lt_one L (div_nonneg hy hx.le)
    ((div_lt_one hx).2 hxy)
  have hlim : Tendsto (fun m : ℕ => (2 : ℝ) ^ L * ((m : ℝ) ^ L * (y / x) ^ m))
      atTop (𝓝 0) := by simpa using hr.const_mul ((2 : ℝ) ^ L)
  have hone : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : ((m : ℝ) + 1) ^ L ≤ (2 * (m : ℝ)) ^ L :=
      pow_le_pow_left₀ (by positivity) (by linarith) L
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ (pow_pos hx _), one_mul,
      ← mul_assoc, ← mul_pow]
    exact (h m hm).trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hy _)))
  norm_num at hone

/-- The growth-rate comparison in nonnegative reals. -/
theorem nnreal_le_of_pow_le_polynomial_mul_pow {x y : ℝ≥0} (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ≥0) + 1) ^ L * y ^ m) : x ≤ y := by
  apply NNReal.coe_le_coe.mp
  apply le_of_pow_le_polynomial_mul_pow y.2 L
  intro m hm
  exact_mod_cast h m hm

/-- A uniformly bounded error between all natural multiples forces equality. -/
theorem eq_of_nat_mul_close {a b C : ℝ}
    (h : ∀ m : ℕ, |(m : ℝ) * (a - b)| ≤ C) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (abs_pos.mpr (sub_ne_zero.mpr hab)) C
  rw [nsmul_eq_mul] at hm
  have hbound := h m
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
  exact hm.not_ge hbound

end SpectralBooks
end LinearAlgebra
end OAI
