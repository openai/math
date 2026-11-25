import OAI.Computability.BorderVNP.Model
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extending the scalar field of an image closure

Section 2.1 uses equations with coefficients in the chosen ambient field. At points
whose coordinates belong to the base field, each linear functional on the extension
transforms an extension-field equation into a base-field polynomial equation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

variable {ι K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Taking a linear functional of a polynomial value at ground-field coordinates
is the same as applying the functional to each coefficient before evaluation. -/
private theorem eval_coefficientFunctional (f : E →ₗ[K] K) (p : MvPolynomial ι E)
    (y : ι → K) :
    eval y (∑ d ∈ p.support, monomial d (f (p.coeff d))) =
      f (eval (algebraMap K E ∘ y) p) := by
  classical
  rw [eval_eq (algebraMap K E ∘ y) p]
  simp only [map_sum, eval_monomial, Finsupp.prod, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro d _
  let a := ∏ i ∈ d.support, y i ^ d i
  have ha : algebraMap K E a = ∏ i ∈ d.support, (algebraMap K E (y i)) ^ d i := by
    simp [a]
  rw [← ha, mul_comm (p.coeff d), ← Algebra.smul_def, f.map_smul, smul_eq_mul, mul_comm]

/-- A ground-field point in the polynomial-vanishing closure of a set stays
in the closure after scalar extension. -/
theorem map_mem_imageClosure {S : Set (ι → K)} {T : Set (ι → E)} {x : ι → K}
    (hST : ∀ y ∈ S, algebraMap K E ∘ y ∈ T) (hx : x ∈ imageClosure S) :
    algebraMap K E ∘ x ∈ imageClosure T := by
  intro p hp
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro f
  rw [← eval_coefficientFunctional]
  apply hx
  intro y hy
  rw [eval_coefficientFunctional, hp _ (hST y hy), map_zero]

end BorderVNP
end Computability
end OAI
