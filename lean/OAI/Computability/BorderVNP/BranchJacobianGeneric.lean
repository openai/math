import OAI.Computability.BorderVNP.BranchJacobianDegree
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Localization.FractionRing

/-! # Generic nonvanishing of the cleared Jacobian equation

Pass from the constant field to its rational function field in the deformation
parameter. Specializing only the chart coordinates at a point off the denominator
leaves the monic determinant pencil. Thus the polynomial exceptional function used
in §9.2 is nonzero over the generic parameter field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped Matrix

variable {K T ι : Type*} [Field K] [Field T] [Algebra K T]
variable [Fintype ι] [DecidableEq ι]

omit [Algebra K T] in
private theorem map_rationalJacobianAt (inc : K →+* T) (z : ι → K) (den : MvPolynomial ι K)
    (num : ι → MvPolynomial ι K) :
    inc.mapMatrix (rationalJacobianAt z den num) =
      rationalJacobianAt (inc ∘ z) (map inc den) (fun i => map inc (num i)) := by
  ext i j
  change inc (_ / _) = _ / _
  simp only [map_div₀, map_sub, map_mul, map_pow, aeval_eq_eval, map_eval, pderiv_map]

omit [Algebra K T] in
/-- The monic determinant pencil remains nonzero after an injective evaluation of the parameter ring. -/
theorem determinant_generic_scalar (inc : K →+* T) (lift : Polynomial K →+* T)
    (hi : Function.Injective lift) (hc : ∀ k, lift (Polynomial.C k) = inc k) (A : Matrix ι ι K) :
    (Matrix.scalar ι (lift Polynomial.X) + inc.mapMatrix A).det ≠ 0 := by
  have he : lift.mapMatrix (Matrix.scalar ι Polynomial.X +
      (Polynomial.C : K →+* Polynomial K).mapMatrix A) =
      Matrix.scalar ι (lift Polynomial.X) + inc.mapMatrix A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar, hc]
    · simp [Matrix.scalar, hij, hc]
  rw [← he, ← RingHom.map_det]
  exact (map_ne_zero_iff lift hi).mpr (determinant_generic_ne_zero A)

/-- Over the rational deformation-parameter field the cleared Jacobian determinant is a
nonzero formal polynomial, for every square rational system with nonzero denominator. -/
theorem generic_jacobianNumerator_ne_zero [Infinite K] [Algebra (Polynomial K) T]
    [IsScalarTower K (Polynomial K) T] [IsFractionRing (Polynomial K) T]
    (den : MvPolynomial ι K) (num : ι → MvPolynomial ι K) (hd : den ≠ 0) :
    (jacobianNumerator (algebraMap (Polynomial K) T Polynomial.X)
      (map (algebraMap K T) den) (fun i => map (algebraMap K T) (num i))).det ≠ 0 := by
  have hz : ∃ z : ι → K, eval z den ≠ 0 := by
    by_contra! h
    exact hd (MvPolynomial.funext fun z => by simpa using h z)
  obtain ⟨z, hz⟩ := hz
  let inc := algebraMap K T
  let lift := algebraMap (Polynomial K) T
  have hd' : aeval (inc ∘ z) (map inc den) ≠ 0 := by
    rw [aeval_eq_eval, ← map_eval]
    exact (map_ne_zero_iff inc inc.injective).mpr hz
  have hc (a : K) : lift (Polynomial.C a) = inc a :=
    (IsScalarTower.algebraMap_apply K (Polynomial K) T a).symm
  have hdet := determinant_generic_scalar inc lift (IsFractionRing.injective _ _) hc
    (rationalJacobianAt z den num)
  rw [map_rationalJacobianAt inc z den num] at hdet
  intro he
  have hh := aeval_jacobianNumerator_det (inc ∘ z) (lift Polynomial.X) (map inc den)
    (fun i => map inc (num i)) hd'
  rw [he, map_zero] at hh
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hd')) hdet hh.symm

end Branch

end BorderVNP
end Computability
end OAI
