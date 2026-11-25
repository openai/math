import OAI.Computability.BorderVNP.CellSparse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! # Little-endian addresses for sparse profile rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

private theorem word_sum (bank : ℕ → Bool) {n : ℕ} (addr : Fin n → ℕ) :
    word bank (List.ofFn addr) = ∑ i, (bank (addr i)).toNat * 2^i.val := by
  induction n with
  | zero => simp [word]
  | succ n ih =>
    rw [List.ofFn_succ, word, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ', Finset.mul_sum]
    congr 1
    · cases bank (addr 0) <;> rfl
    · apply Finset.sum_congr rfl
      intro i _
      ac_rfl

/-- The sparse reader and the crossing code assign exactly the same
little-endian index, including the empty word. -/
theorem word_ofFn (bank : ℕ → Bool) {n : ℕ} (addr : Fin n → ℕ) :
    word bank (List.ofFn addr) = (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bank (addr i)))).val := by
  rw [word_sum, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases bank (addr i) <;> rfl

end CellSparse

end BorderVNP
end Computability
end OAI
