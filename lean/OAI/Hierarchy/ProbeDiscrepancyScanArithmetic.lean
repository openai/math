import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic

namespace OAI
/-! # Integral bounds on deposited scores and the ceiled vote threshold -/
namespace Hierarchy.AdaptiveProbe
open scoped BigOperators

theorem deposited_sum_le {rows : ℕ} (value : Fin rows→ℕ) (precision : ℕ) (ceiling : ℝ)
    (hp : 0<precision) (bounded : ∀i,(value i:ℝ)/precision ≤ ceiling) :
    (∑i,value i) ≤ rows*⌈ceiling*(precision:ℝ)⌉₊ := by
  have cell (i : Fin rows) : value i≤⌈ceiling*(precision:ℝ)⌉₊ := by
    have pos : 0<(precision:ℝ) := Nat.cast_pos.mpr hp
    exact_mod_cast ((div_le_iff₀ pos).mp (bounded i)).trans (Nat.le_ceil _)
  calc
    (∑i,value i)≤∑_i : Fin rows,⌈ceiling*(precision:ℝ)⌉₊ :=
      Finset.sum_le_sum (fun i _=>cell i)
    _=rows*⌈ceiling*(precision:ℝ)⌉₊ := by simp []

theorem ceiled_score_le (score : ℝ) (rows precision : ℕ) :
    ⌈score*(rows:ℝ)*(precision:ℝ)⌉₊≤⌈score*(precision:ℝ)⌉₊*rows := by
  rw [Nat.ceil_le,Nat.cast_mul]
  calc
    score*rows*precision=(score*precision)*(rows:ℝ) := by ring
    _≤(⌈score*(precision:ℝ)⌉₊:ℝ)*(rows:ℝ) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg rows)

end Hierarchy.AdaptiveProbe

end OAI
