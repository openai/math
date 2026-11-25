import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace OAI
/-! # The radix prefix read by a high-to-low digit scan -/

namespace Hierarchy.FactorBucketRAM

open scoped BigOperators

variable {d R : ℕ}

/-- Read a digit at its little-endian coordinate. -/
def keyDigit (a : Fin d → Fin R) (n : ℕ) : ℕ :=
  if h : n < d then (a ⟨n,h⟩).val else 0

/-- The base-`R` number represented by the first `j` high digits. -/
def keyPrefix (a : Fin d → Fin R) (j : ℕ) : ℕ :=
  ∑ i : Fin j, keyDigit a (d-j+i.val) * R^i.val

@[simp] theorem keyPrefix_zero (a : Fin d → Fin R) : keyPrefix a 0 = 0 := by simp [keyPrefix]

theorem keyPrefix_succ (a : Fin d → Fin R) (j : ℕ) (hj : j<d) :
    keyPrefix a (j+1) = keyPrefix a j * R + keyDigit a (d-1-j) := by
  unfold keyPrefix
  rw [Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.val_zero, Nat.add_zero, pow_zero, mul_one]
  rw [Nat.add_comm (∑ _ : Fin j, _)]
  congr 1
  · congr 1
    omega
  · apply Finset.sum_congr rfl
    intro i _
    have eq : d-(j+1)+i.succ.val = d-j+i.val := by simp only [Fin.val_succ]; omega
    rw [eq, Fin.val_succ, pow_succ, Nat.mul_assoc]

theorem keyPrefix_done (a : Fin d → Fin R) :
    keyPrefix a d = (finFunctionFinEquiv a).val := by
  rw [finFunctionFinEquiv_apply]
  simp [keyPrefix,keyDigit]

end Hierarchy.FactorBucketRAM

end OAI
