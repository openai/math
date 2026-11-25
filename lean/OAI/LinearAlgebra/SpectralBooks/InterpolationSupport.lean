import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integer support of the coefficient extraction

For the proof of intersecting submodularity, `k` indexes the sites of the
intersection other than its first site. At the first site the labels are `h`
and `a`, the other labels are `v`, and the newly adjoined site has label `g`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {q k : ℕ}

/-- Exponent of the product of the local monomials. -/
def supportExponent (h g a : Fin q) (v : Fin k → Fin q) : ℕ :=
  (q - 1 - h.val + k * a.val) + (∑ j, (q - 1 - (v j).val)) + g.val

private theorem complement_sum_add (v : Fin k → Fin q) :
    (∑ j, (q - 1 - (v j).val)) + (∑ j, (v j).val) = k * (q - 1) := by
  rw [← Finset.sum_add_distrib]
  have h (j : Fin k) : q - 1 - (v j).val + (v j).val = q - 1 := by
    have := (v j).isLt
    omega
  simp [h]

/-- Extracting the coefficient at degree `(k + 1) * (q - 1)` selects the
specified integer equation independently of the characteristic of the field. -/
theorem supportExponent_eq_iff (h g a : Fin q) (v : Fin k → Fin q) :
    supportExponent h g a v = (k + 1) * (q - 1) ↔
      (g.val : ℤ) = h.val + (∑ j, ((v j).val : ℤ)) - (k : ℤ) * a.val := by
  rw [eq_sub_iff_add_eq]
  have heq : ((g.val + k * a.val : ℕ) : ℤ) = (g.val : ℤ) + (k : ℤ) * a.val := by
    norm_cast
  have hsum : ((h.val + ∑ j, (v j).val : ℕ) : ℤ) = (h.val : ℤ) + ∑ j, ((v j).val : ℤ) := by
    norm_cast
  rw [← heq, ← hsum, Nat.cast_inj]
  have hcomp := complement_sum_add v
  have hh := h.isLt
  simp only [supportExponent, Nat.add_mul, Nat.one_mul]
  omega

/-- The degree bound gives `2 * (k + 1) * (q - 1) + 1` evaluation points. -/
theorem supportExponent_le (h g a : Fin q) (v : Fin k → Fin q) :
    supportExponent h g a v ≤ 2 * (k + 1) * (q - 1) := by
  have ha : a.val ≤ q - 1 := by have := a.isLt; omega
  have hg : g.val ≤ q - 1 := by have := g.isLt; omega
  have hmul := Nat.mul_le_mul_left k ha
  have hcomp := complement_sum_add v
  rw [supportExponent, Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
  omega

end SpectralBooks
end LinearAlgebra
end OAI
