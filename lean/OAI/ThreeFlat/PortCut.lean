import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
/-! # Sparse cuts from the scalar quadratic Poincaré inequality -/

namespace ThreeFlat

open scoped BigOperators

/-- The size of a cut, counting edges with their multiplicities. -/
noncomputable def cutEdgeCount {V E : Type*} [Fintype E]
    (l r : E → V) (s : Finset V) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => (l e ∈ s) ≠ (r e ∈ s)).card

/-- A scalar Poincaré inequality, applied to a characteristic function, bounds
the size of each set containing at most half the vertices by its edge boundary. -/
theorem cutEdgeCount_of_scalar_poincare {V E : Type*} [Fintype V] [Fintype E]
    (l r : E → V) {C : ℝ} (s : Finset V) (hs : s.card * 2 ≤ Fintype.card V)
    (h : ∀ f : V → ℝ, (∑ i, ∑ j, (f i - f j) ^ 2) ≤
      C * ∑ e, (f (l e) - f (r e)) ^ 2) :
    (s.card : ℝ) * Fintype.card V ≤ C * cutEdgeCount l r s := by
  classical
  let f (i : V) : ℝ := if i ∈ s then 1 else 0
  have hf : ∑ i, f i = (s.card : ℝ) := by
    simp [f]
  have hdiff (i j : V) :
      (f i - f j) ^ 2 = f i + f j - 2 * f i * f j := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> norm_num [f, hi, hj]
  have hrow (i : V) : ∑ j, (f i - f j) ^ 2 =
      (Fintype.card V : ℝ) * f i + s.card - 2 * f i * s.card := by
    simp only [hdiff, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hf]
  have hpair : (∑ i, ∑ j, (f i - f j) ^ 2) =
      2 * (s.card : ℝ) * (Fintype.card V - s.card) := by
    simp only [hrow, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]
    ring
  have hedge : (∑ e, (f (l e) - f (r e)) ^ 2) = (cutEdgeCount l r s : ℝ) := by
    unfold cutEdgeCount
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hl : l e ∈ s <;> by_cases hr : r e ∈ s <;> norm_num [f, hl, hr]
  have bound := h f
  rw [hpair, hedge] at bound
  have hhalf : (s.card : ℝ) * 2 ≤ Fintype.card V := by exact_mod_cast hs
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  nlinarith [mul_nonneg hcard (sub_nonneg.mpr hhalf)]

end ThreeFlat

end OAI
