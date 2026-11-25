import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Transport by moving one site at a time

Summing single-index price estimates along local moves gives the full transport
bound. Symmetry of the move costs supplies the bound for the absolute difference.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

section

variable {I J : Type*} [Fintype I]

/-- A price with a one-index transport bound has a global one-sided transport bound. -/
theorem price_transport_le_sum (p : (I → J) → ℝ) (d : J → J → ℝ) (c : I → ℝ)
    (step : ∀ (a b : I → J) (i : I), (∀ j, j ≠ i → a j = b j) →
      p b ≤ p a + d (a i) (b i) * c i)
    (x y : I → J) : p y ≤ p x + ∑ i, d (x i) (y i) * c i := by
  classical
  let move (s : Finset I) (i : I) := if i ∈ s then y i else x i
  have bound (s : Finset I) :
      p (move s) ≤ p x + ∑ i ∈ s, d (x i) (y i) * c i := by
    induction s using Finset.induction_on with
    | empty => simp [move]
    | @insert i s hi ih =>
      have hs := step (move s) (move (insert i s)) i fun j hj => by simp [move, hj]
      simp only [move, hi, ↓reduceIte, Finset.mem_insert_self] at hs
      rw [Finset.sum_insert hi, ← add_assoc, add_right_comm]
      exact hs.trans (add_le_add_left ih _)
  simpa [move] using bound Finset.univ

/-- Symmetric costs bound the absolute change of the price between placements. -/
theorem abs_price_sub_le_transport (p : (I → J) → ℝ) (d : J → J → ℝ) (c : I → ℝ)
    (symm : ∀ a b, d a b = d b a)
    (step : ∀ (a b : I → J) (i : I), (∀ j, j ≠ i → a j = b j) →
      p b ≤ p a + d (a i) (b i) * c i)
    (x y : I → J) : |p x - p y| ≤ ∑ i, d (x i) (y i) * c i := by
  obtain hxy := price_transport_le_sum p d c step x y
  obtain hyx := price_transport_le_sum p d c step y x
  simp_rw [fun i => symm (y i) (x i)] at hyx
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end

end SpectralBooks
end LinearAlgebra
end OAI
