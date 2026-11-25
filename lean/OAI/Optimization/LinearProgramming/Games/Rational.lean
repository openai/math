import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games

/-- The separation used for both integer cycle means and the stochastic values. -/
theorem rat_separation {A : ℕ} {x y : ℚ} (hx : x.den ≤ A) (hy : y.den ≤ A)
    (hne : x ≠ y) : 1 / (A : ℝ)^2 ≤ |(x : ℝ) - y| := by
  have hxpos : 0 < (x.den : ℝ) := by exact_mod_cast x.pos
  have hypos : 0 < (y.den : ℝ) := by exact_mod_cast y.pos
  have hA : 0 < (A : ℝ) := by exact_mod_cast lt_of_lt_of_le x.pos hx
  have cross : x.num * (y.den : ℤ) - y.num * (x.den : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (fun he => hne (Rat.eq_iff_mul_eq_mul.mpr (by simpa [mul_comm] using he)))
  have hz : (1 : ℝ) ≤ |(x.num : ℝ) * y.den - (y.num : ℝ) * x.den| := by
    exact_mod_cast Int.one_le_abs cross
  have eqn : (x : ℝ) - y =
      ((x.num : ℝ) * y.den - (y.num : ℝ) * x.den) / (x.den * y.den) := by
    rw [Rat.cast_def x, Rat.cast_def y]
    field_simp
  rw [eqn, abs_div, abs_of_pos (mul_pos hxpos hypos)]
  apply le_trans _ ((div_le_div_iff_of_pos_right (mul_pos hxpos hypos)).mpr hz)
  apply one_div_le_one_div_of_le (mul_pos hxpos hypos)
  rw [sq]
  exact mul_le_mul (by exact_mod_cast hx) (by exact_mod_cast hy) hypos.le hA.le

/-- A real approximation of radius (1/(8A^2)) determines the bounded-denominator
value uniquely. Legendre's theorem places it among the convergents of the approximation. -/
theorem recover_rational_value {A : ℕ} {z : ℝ} {g : ℚ} (hg : g.den ≤ A)
    (hz : |z - g| ≤ 1 / (8 * (A : ℝ)^2)) :
    (∃ k, z.convergent k = g) ∧
      ∀ q : ℚ, q.den ≤ A → |z - q| ≤ 1 / (8 * (A : ℝ)^2) → q = g := by
  have hp : 0 < (g.den : ℝ) := by exact_mod_cast g.pos
  have hA : 0 < (A : ℝ) := by exact_mod_cast lt_of_lt_of_le g.pos hg
  have hg' : (g.den : ℝ)^2 ≤ (A : ℝ)^2 := by
    exact pow_le_pow_left₀ hp.le (by exact_mod_cast hg) 2
  constructor
  · obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent (ξ := z) (q := g)
      (hz.trans_lt (one_div_lt_one_div_of_lt (by positivity) (by nlinarith [sq_pos_of_pos hA])))
    exact ⟨n, hn.symm⟩
  · intro q hq hqz
    by_contra hne
    have sep := rat_separation hq hg hne
    have ht := abs_sub_le (q : ℝ) z (g : ℝ)
    rw [abs_sub_comm (q : ℝ) z] at ht
    have : (1 : ℝ) / (A : ℝ)^2 > 1 / (8*(A:ℝ)^2) + 1 / (8*(A:ℝ)^2) := by
      field_simp
      norm_num
    linarith

/-- In the deterministic game, a strict error smaller than the separation of
two integer cycle means suffices for the exact lower-bound inequality. -/
theorem round_cycle_lower_bound {n : ℕ} {actual value : ℚ}
    (ha : actual.den ≤ n) (hv : value.den ≤ n)
    (h : (value : ℝ) - 1 / (n : ℝ)^2 < actual) : value ≤ actual := by
  by_contra! hlt
  have hs := rat_separation ha hv hlt.ne
  rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hlt))] at hs
  linarith

end Games
end LinearProgramming
end Optimization
end OAI
