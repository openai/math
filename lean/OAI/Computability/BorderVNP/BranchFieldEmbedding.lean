import OAI.Computability.BorderVNP.BranchCurveArithmeticDescent
import OAI.Computability.BorderVNP.BranchAffineDescent
import Mathlib.FieldTheory.Finite.Valuation

/-!
# Embedding the advice-field parameter and its equations

The rational parameter field over a finite advice field embeds in the rational
parameter field over its algebraic closure by sending `t` to `t`. Substitution
of the generic parameter in the branch equations commutes with this embedding.
All polynomial expressions in the finite constants and a regular parameter
are regular for any valuation centered on the geometric component.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- Rational functions in the deformation parameter over the indicated coefficient field. -/
abbrev DeformationField (E : Type*) [Field E] := FractionRing (Polynomial E)

/-- Scalar extension of rational functions, fixing the deformation parameter. -/
noncomputable def deformationMap {E K : Type*} [Field E] [Field K] (f : E →+* K) :
    DeformationField E →+* DeformationField K :=
  IsFractionRing.lift (g := (algebraMap (Polynomial K) (DeformationField K)).comp
    (Polynomial.mapRingHom f)) ((IsFractionRing.injective (Polynomial K) (DeformationField K)).comp
    (Polynomial.map_injective f f.injective))

/-- The rational-function embedding acts on polynomials by ordinary coefficient extension. -/
theorem deformationMap_polynomial {E K : Type*} [Field E] [Field K] (f : E →+* K) (p : Polynomial E) :
    deformationMap f (algebraMap (Polynomial E) _ p) =
      algebraMap (Polynomial K) (DeformationField K) (p.map f) := by
  unfold deformationMap
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- The rational-function embedding agrees with the chosen embedding of constant fields. -/
theorem deformationMap_constant {E K : Type*} [Field E] [Field K] (f : E →+* K) (c : E) :
    deformationMap f (algebraMap E (DeformationField E) c) =
      algebraMap K (DeformationField K) (f c) := by
  rw [IsScalarTower.algebraMap_apply E (Polynomial E) (DeformationField E),
    deformationMap_polynomial, IsScalarTower.algebraMap_apply K (Polynomial K) (DeformationField K)]
  simp

/-- A row in variables `(X,t)` considered as a polynomial in `X` over `E(t)`. -/
noncomputable def genericRow {σ E : Type*} [Field E] :
    MvPolynomial (Option σ) E →+* MvPolynomial σ (DeformationField E) :=
  eval₂Hom (C.comp (algebraMap E (DeformationField E)))
    (fun o => o.elim (C (algebraMap (Polynomial E) (DeformationField E) Polynomial.X)) X)

/-- Mapping a generic row from `E(t)` to `K(t)` gives the identical row formed over `K`. -/
theorem genericRow_map {σ E K : Type*} [Field E] [Field K] (f : E →+* K)
    (p : MvPolynomial (Option σ) E) :
    map (deformationMap f) (genericRow p) = genericRow (map f p) := by
  have e : (map (σ := σ) (deformationMap f)).comp genericRow =
      genericRow.comp (map (σ := Option σ) f) := by
    apply ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, genericRow, eval₂Hom_C, map_C, deformationMap_constant]
    · intro i
      cases i <;> simp [genericRow, deformationMap_polynomial]
  exact RingHom.congr_fun e p

/-- A valuation ring contains the image of every element of a finite constant field. -/
theorem finite_constants_regular {E L : Type*} [Field E] [Finite E] [Field L]
    (f : E →+* L) (V : ValuationSubring L) (a : E) : f a ∈ V := by
  let := f.toAlgebra
  exact (V.valuation_le_one_iff _).mp (FiniteField.valuation_algebraMap_le_one V.valuation a)

/-- Over finite constants it suffices for the parameter to be regular in order to
obtain the inclusion of the entire polynomial parameter ring. -/
theorem polynomial_parameters_regular {E L : Type*} [Field E] [Finite E] [Field L]
    (i : Polynomial E →+* L) (V : ValuationSubring L) (ht : i Polynomial.X ∈ V) :
    ∀ a : Polynomial E, i a ∈ V := by
  intro a
  induction a using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact V.toSubring.add_mem hp hq
  | monomial n e =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact V.toSubring.mul_mem (finite_constants_regular (i.comp Polynomial.C) V e) (V.toSubring.pow_mem ht _)

end Branch

end BorderVNP
end Computability
end OAI
