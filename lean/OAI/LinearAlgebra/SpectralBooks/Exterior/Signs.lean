import Mathlib.Algebra.Ring.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-! # Signs of exterior creation and contraction on subset coordinates -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Exterior

variable (K : Type*) [CommRing K] {Q : ℕ}

/-- Sign for inserting or removing an index in the ordered exterior monomial. -/
def sign (i : Fin Q) (S : Finset (Fin Q)) : K :=
  (-1) ^ (S.filter (· < i)).card

@[simp] theorem sign_sq (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i S * sign K i S = 1 := by
  simp [sign, ← mul_pow]

@[simp] theorem sign_erase_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (S.erase i) = sign K i S := by
  simp [sign, Finset.filter_erase]

@[simp] theorem sign_insert_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (insert i S) = sign K i S := by
  simp [sign, Finset.filter_insert]

theorem sign_insert (i j : Fin Q) (S : Finset (Fin Q)) (hi : i ∉ S) :
    sign K j (insert i S) = if i < j then -sign K j S else sign K j S := by
  by_cases h : i < j <;> simp [sign, Finset.filter_insert, h, hi, pow_succ]

/-- The two orders of creation at one index and contraction at another
give opposite coefficients, including in characteristic two. -/
theorem sign_cancel {i j : Fin Q} {S : Finset (Fin Q)} (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    sign K i S * sign K j (insert i S) + sign K j S * sign K i (S.erase j) = 0 := by
  have he := sign_insert K j i (S.erase j) (Finset.notMem_erase j S)
  rw [Finset.insert_erase hj] at he
  rw [sign_insert K i j S hi]
  rcases lt_or_gt_of_ne hij with h | h
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring

end Exterior

end SpectralBooks
end LinearAlgebra
end OAI
