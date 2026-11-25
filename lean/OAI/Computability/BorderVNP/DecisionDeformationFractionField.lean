import OAI.Computability.BorderVNP.DecisionDeformationMotion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # The function field of the deformation curve

A dominant parameter on a one-dimensional affine domain gives a finite extension
of the rational function field. The two explicit homomorphisms below evaluate
polynomials and rational functions at that same parameter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open scoped nonZeroDivisors

variable (E : Type*) {A : Type*} [Field E] [CommRing A] [IsDomain A] [Algebra E A]

/-- Evaluate a parameter polynomial in the coordinate ring and include its value
in the curve's fraction field. -/
noncomputable def parameterPolynomialMap (t : A) : Polynomial E →+* FractionRing A :=
  (algebraMap A (FractionRing A)).comp (Polynomial.aeval (R := E) t).toRingHom

/-- The rational-function embedding induced by a dominant parameter. -/
noncomputable def parameterFractionMap (t : A) (ht : Function.Injective (Polynomial.aeval (R := E) t)) :
    FractionRing (Polynomial E) →+* FractionRing A :=
  IsFractionRing.lift (g := parameterPolynomialMap E t) ((IsFractionRing.injective A _).comp ht)

/-- The rational-function embedding extends polynomial evaluation. -/
theorem parameterFractionMap_polynomial (t : A) (ht : Function.Injective (Polynomial.aeval (R := E) t))
    (p : Polynomial E) :
    parameterFractionMap E t ht (algebraMap _ (FractionRing (Polynomial E)) p) =
      parameterPolynomialMap E t p :=
  IsFractionRing.lift_algebraMap _ _

private theorem fraction_trdeg_one [Algebra.FiniteType E A] (hd : ringKrullDim A = 1) :
    Algebra.trdeg E (FractionRing A) = 1 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := A)
  have hh : (m.height : WithBot ℕ∞) = 1 :=
    (Branch.affineDomain_point_height (K := E) m).trans hd
  have h1 := trdeg_at_closed_point (E := E) (d := 1) m (by exact_mod_cast hh)
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ A⁰
  rw [← trdeg_add_eq E A, trdeg_eq_zero (R := A), add_zero, h1, Nat.cast_one]

/-- A compatible embedding of the rational parameter field has finite degree
in the function field of an affine integral curve. -/
theorem affineCurveFraction_finite [Algebra.FiniteType E A] (hd : ringKrullDim A = 1)
    [Algebra (FractionRing (Polynomial E)) (FractionRing A)]
    [IsScalarTower E (FractionRing (Polynomial E)) (FractionRing A)] :
    FiniteDimensional (FractionRing (Polynomial E)) (FractionRing A) := by
  let K := FractionRing (Polynomial E)
  let L := FractionRing A
  have : Algebra.IsAlgebraic (Polynomial E) K := IsLocalization.isAlgebraic _ (Polynomial E)⁰
  have hK : Algebra.trdeg E K = 1 := by
    rw [← trdeg_add_eq E (Polynomial E), trdeg_eq_zero (R := Polynomial E), add_zero, Polynomial.trdeg_of_isDomain]
  have hL : Algebra.trdeg E L = 1 := fraction_trdeg_one E hd
  have h := lift_trdeg_add_eq E K L
  rw [hK, hL, Cardinal.lift_one, Cardinal.lift_one] at h
  have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp (by
    by_contra hne
    have hpos := Cardinal.lift_le.mpr (Cardinal.one_le_iff_ne_zero.mpr hne)
    rw [Cardinal.lift_one] at hpos
    have hbad := (add_le_add_right hpos 1).trans h.le
    norm_num at hbad)
  have : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization _ A⁰
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.comp E A L
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp E K L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- The maps evaluating the parameter determine the two scalar towers needed for
places of the function field, and make the function field a finite extension. -/
theorem affineCurveParameter [Algebra.FiniteType E A] (t : A)
    (ht : Function.Injective (Polynomial.aeval (R := E) t)) (hd : ringKrullDim A = 1) :
    letI := (parameterPolynomialMap E t).toAlgebra
    letI := (parameterFractionMap E t ht).toAlgebra
    IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) (FractionRing A) ∧
      IsScalarTower E (FractionRing (Polynomial E)) (FractionRing A) ∧
      FiniteDimensional (FractionRing (Polynomial E)) (FractionRing A) := by
  let := (parameterPolynomialMap E t).toAlgebra
  let := (parameterFractionMap E t ht).toAlgebra
  have hpoly : IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) (FractionRing A) :=
    .of_algebraMap_eq (fun p => (parameterFractionMap_polynomial E t ht p).symm)
  have : IsScalarTower E (Polynomial E) (FractionRing A) := .of_algebraMap_eq (fun x => by
    change algebraMap E (FractionRing A) x = algebraMap A (FractionRing A)
      (Polynomial.aeval t (Polynomial.C x))
    rw [Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply])
  have hE : IsScalarTower E (FractionRing (Polynomial E)) (FractionRing A) :=
    IsScalarTower.to₁₃₄ E (Polynomial E) _ _
  exact ⟨hpoly, hE, affineCurveFraction_finite E hd⟩

end Decision

end BorderVNP
end Computability
end OAI
