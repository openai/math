import OAI.LinearAlgebra.SpectralBooks.Fermion.Fermion
import Mathlib.Data.Finset.Sort

/-! # Integer matrix elements of the normal-ordered fermion fields

In a normal product the first differentiated field can create on the output
state, or pass through the remaining fields and delete on the input state.
This recurrence computes every coefficient using only finite sums of integers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset
open scoped BigOperators

/-- Sign for creation or deletion in the ordered basis of finite mode sets. -/
def wedgeSign (r : ℕ) (S : State) : ℤ := (-1) ^ (S.filter (· < r)).card

/-- Hasse coefficient of the negative Laurent monomial with exponent `-r-1`. -/
def negativeChoose (r j : ℕ) : ℤ := (-1) ^ j * ((r+j).choose j : ℤ)

/-- Coefficients of the normal product for an ordered list of Hasse derivatives.
The row is the output state and the column is the input state. -/
def listMode : List ℕ → ℤ → State → State → ℤ
  | [], b, α, β => if b = 0 ∧ α = β then 1 else 0
  | j :: l, b, α, β =>
      (∑ r ∈ α, (r.choose j : ℤ) * wedgeSign r α *
        listMode l (b-r+j) (α.erase r) β) +
      (-1) ^ l.length * ∑ r ∈ β, negativeChoose r j * wedgeSign r β *
        listMode l (b+r+1+j) α (β.erase r)

/-- The coefficient of `z^b` in the field indexed by the increasing mode list `I`. -/
def blockMode (I : State) := listMode (I.sort (· ≤ ·))

private theorem weight_erase_add {s : State} {r : ℕ} (hr : r ∈ s) :
    weight (s.erase r) + (2*r+1) = weight s := by
  exact Finset.sum_erase_add _ _ hr

def listWeight (l : List ℕ) := (l.map (fun r ↦ 2*r+1)).sum

/-- Every nonzero term of a normal field coefficient shifts doubled energy
by twice its Laurent exponent plus the doubled energy of its derivative list. -/
theorem weight_eq_of_listMode_ne_zero {l : List ℕ} {b : ℤ} {α β : State}
    (h : listMode l b α β ≠ 0) : (weight α : ℤ) = weight β + 2*b + listWeight l := by
  induction l generalizing b α β with
  | nil =>
    have he : b = 0 ∧ α = β := by simpa [listMode] using h
    simp [he.1, he.2, listWeight]
  | cons j l ih =>
    rw [listMode] at h
    have step {x y : ℤ} (hne : x + y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by omega
    rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
    rcases step h with hc | ha
    · obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      have htail := ih ((mul_ne_zero_iff.mp hterm).2)
      have hw := weight_erase_add hr
      omega
    · obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((mul_ne_zero_iff.mp ha).2)
      have htail := ih ((mul_ne_zero_iff.mp hterm).2)
      have hw := weight_erase_add hr
      omega

private theorem listWeight_sort (I : State) : listWeight (I.sort (· ≤ ·)) = weight I := by
  change (Multiset.map (fun r : ℕ ↦ 2*r+1) (I.sort (· ≤ ·) : Multiset ℕ)).sum = _
  rw [Finset.sort_eq]
  rfl

theorem weight_eq_of_blockMode_ne_zero {I α β : State} {b : ℤ}
    (h : blockMode I b α β ≠ 0) : (weight α : ℤ) = weight β + 2*b + weight I := by
  simpa only [listWeight_sort] using weight_eq_of_listMode_ne_zero h

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
