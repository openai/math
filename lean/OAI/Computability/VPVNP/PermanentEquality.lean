import OAI.Computability.VPVNP.PermanentCoefficient
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# An equality gadget for the permanent

The three internal rows have column weights `(-b,-b,b)`, `(-1,-1,1)`,
and `(1,1,1)`. The first two rows can also exit with weights `A` and `B`.
Taking the coefficient that fills every internal column exactly once
cancels the choices that use only one incoming port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Product of the three internal row forms, including the two possible exits. -/
noncomputable def equalityRows (b A B : R) : MvPolynomial (Fin 3) R :=
  (-C b * X 0 - C b * X 1 + C b * X 2 + C A) *
    (-X 0 - X 1 + X 2 + C B) * (X 0 + X 1 + X 2)

/-- Weights of the internal directed edges, in port order. -/
def equalityMatrix (b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![-b, -b, b; -1, -1, 1; 1, 1, 1]

/-- Each row chooses an internal column or exits the gadget. -/
theorem equalityRows_eq_prod (b A B : R) :
    equalityRows b A B = ∏ i : Fin 3,
      ((∑ j : Fin 3, C (equalityMatrix b i j) * X j) + C (![A, B, 0] i)) := by
  rw [Fin.prod_univ_three]
  simp [equalityRows, equalityMatrix, Fin.sum_univ_three, sub_eq_add_neg]

private theorem eq_fullDegree_three (d : Fin 3 →₀ ℕ) :
    d = fullDegree (Fin 3) ↔ d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₀, h₁, h₂⟩
    ext j
    fin_cases j <;> simpa

/-- When neither port enters, the internal cycle covers have total weight
one. When both enter, the two exits contribute `A * B`. -/
theorem coeff_equalityRows (b A B : R) (hb : -2 * b = 1) (i₀ i₁ : Bool) :
    ((if i₀ then X 0 else 1) * (if i₁ then X 1 else 1) *
      equalityRows b A B).coeff (fullDegree (Fin 3)) =
      if i₀ then (if i₁ then A * B else 0) else (if i₁ then 0 else 1) := by
  cases i₀ <;> cases i₁ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, mul_one] <;>
    simp only [equalityRows, X, C_apply, sub_eq_add_neg, add_mul, mul_add, neg_mul, mul_neg,
      monomial_mul_monomial, AddMonoidAlgebra.coeff_add, coeff_neg, coeff_monomial, eq_fullDegree_three,
      Finsupp.add_apply, Finsupp.zero_apply, Finsupp.single_apply] <;>
    simp (config := { decide := true })
  · calc
      _ = -2 * b := by ring
      _ = 1 := hb
  all_goals ring

/-- In a field of characteristic different from two, the required weight
`b = −1/2` remains normalized after applying any coefficient homomorphism. -/
theorem map_neg_half_normalized {F : Type*} [Field F] (q : ℕ) [CharP F q]
    (hq : q ≠ 2) (φ : F →+* R) : -2 * φ (-(2 : F)⁻¹) = 1 := by
  have h₂ : (2 : F) ≠ 0 := Ring.two_ne_zero (by simpa [ringChar.eq F q] using hq)
  have h : -(2 : F) * (-(2 : F)⁻¹) = 1 := by simp [h₂]
  simpa [map_ofNat] using congrArg φ h

end PermanentReduction

end VPVNP
end Computability
end OAI
