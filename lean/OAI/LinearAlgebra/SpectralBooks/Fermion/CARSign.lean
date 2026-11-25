import OAI.LinearAlgebra.SpectralBooks.Fermion.WickModes

/-! # Signs of the ordered fermion basis

Changing the occupation of mode `j` reverses the wedge sign at `i` exactly
when `j < i`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset

theorem wedgeSign_insert (i : ℕ) {s : State} {j : ℕ} (hj : j ∉ s) :
    wedgeSign i (insert j s) = (if j < i then -1 else 1) * wedgeSign i s := by
  by_cases hji : j < i
  · simp [wedgeSign, filter_insert, hji, Finset.notMem_mono (filter_subset _ _) hj, pow_succ]
  · simp [wedgeSign, filter_insert, hji]

theorem wedgeSign_erase (i : ℕ) {s : State} {j : ℕ} (hj : j ∈ s) :
    wedgeSign i (s.erase j) = (if j < i then -1 else 1) * wedgeSign i s := by
  have h := wedgeSign_insert i (s := s.erase j) (j := j) (notMem_erase _ _)
  rw [insert_erase hj] at h
  rw [h]
  split <;> simp

theorem wedgeSign_mul_self (i : ℕ) (s : State) : wedgeSign i s * wedgeSign i s = 1 := by
  simp [wedgeSign, ← mul_pow]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
