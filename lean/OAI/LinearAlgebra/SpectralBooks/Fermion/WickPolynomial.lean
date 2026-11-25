import OAI.LinearAlgebra.SpectralBooks.Fermion.WickModes
import Mathlib.Algebra.Polynomial.Laurent

/-! # Laurent polynomial entries of mixed normal products

Evaluate the first formal variable at one and the second at the Laurent indeterminate.
For fixed input and output states, a creation at the left can use only an output mode,
and a deletion at the right can use only an input mode. The resulting Laurent polynomial
does not depend on the truncation once these two states fit inside the cutoff.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open LaurentPolynomial

/-- A field is labeled by the choice of variable and its divided derivative order. -/
abbrev FieldLabel := Bool × ℕ

/-- The first variable is set to one, and the second is the Laurent indeterminate. -/
def fieldExponent (side : Bool) (d : ℤ) : ℤ := if side then d else 0

def creationCoeff (f : FieldLabel) (r : ℕ) : LaurentPolynomial ℤ :=
  C (r.choose f.2 : ℤ) * T (fieldExponent f.1 ((r : ℤ) - f.2))

def annihilationCoeff (f : FieldLabel) (r : ℕ) : LaurentPolynomial ℤ :=
  C (negativeChoose r f.2) * T (fieldExponent f.1 (-(r : ℤ) - 1 - f.2))

/-- The mixed two-block normal product between basis states, as a finite polynomial. -/
def mixedNormal : List FieldLabel → State → State → LaurentPolynomial ℤ
  | [], α, β => if α = β then 1 else 0
  | f :: l, α, β =>
    (∑ r ∈ α, creationCoeff f r * C (wedgeSign r α) * mixedNormal l (α.erase r) β) +
    (-1) ^ l.length * ∑ r ∈ β,
      annihilationCoeff f r * C (wedgeSign r β) * mixedNormal l α (β.erase r)

/-- The only possible Laurent exponent of a monochromatic normal product. -/
def modeDegree (l : List ℕ) (α β : State) : ℤ :=
  ((weight α : ℤ) - weight β - listWeight l) / 2

theorem modeDegree_of_listMode_ne_zero {l : List ℕ} {α β : State} {b : ℤ}
    (h : listMode l b α β ≠ 0) : modeDegree l α β = b := by
  unfold modeDegree
  have hw := weight_eq_of_listMode_ne_zero h
  omega

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
