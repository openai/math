import OAI.Computability.BorderVNP.BranchCurvePlace
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The discrete place of a separably parametrized curve

A valuation of a finite separable extension of the rational function field
centered above zero on the parameter line is the localization at its center
of the integral closure of the line. This gives a discrete valuation ring
even when the original affine parameter coordinates have poles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

/-- A valuation subring centered at a nonzero prime of a Dedekind subring with
the same fraction field is the local ring at its center. -/
theorem valuation_eq_localization {L : Type*} [Field L] (B : Subring L)
    [IsDedekindDomain B] [IsFractionRing B L]
    (V : ValuationSubring L) (hBV : B ≤ V.toSubring)
    (hne : (IsLocalRing.maximalIdeal V).comap (Subring.inclusion hBV) ≠ ⊥) :
    (LocalSubring.ofPrime B ((IsLocalRing.maximalIdeal V).comap
      (Subring.inclusion hBV))).toSubring = V.toSubring := by
  let i := Subring.inclusion hBV
  let P := (IsLocalRing.maximalIdeal V).comap i
  let W := (LocalSubring.ofPrime B P).toSubring
  have : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hne W
  have : IsFractionRing W L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl W L
  have hu (a : P.primeCompl) : IsUnit (i a.val) := by
    by_contra h
    exact a.property h
  let f : W →+* V := IsLocalization.lift (S := W) hu
  have hf (x : B) : f (algebraMap B W x) = i x := IsLocalization.lift_eq hu x
  have incl : V.subtype.comp f = W.subtype := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext x
    change (f (algebraMap B W x) : L) = x.val
    rw [hf]
    rfl
  have : IsLocalHom f := by
    constructor
    intro w hw
    obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl w
    apply (IsLocalization.AtPrime.isUnit_mk'_iff W P x y).mpr
    have hmul : f (IsLocalization.mk' W x y) * i y.val = i x := by
      rw [← hf, ← hf, ← map_mul, IsLocalization.mk'_spec]
    change ¬ ¬ IsUnit (i x)
    exact not_not.mpr (hmul ▸ hw.mul (hu y))
  have surj := (bijective_rangeRestrict_comp_of_valuationRing f V.subtype incl).surjective
  change W = V.toSubring
  apply le_antisymm
  · intro x hx
    have e : (f ⟨x, hx⟩ : L) = x := RingHom.congr_fun incl ⟨x, hx⟩
    rw [← e]
    exact (f ⟨x, hx⟩).property
  · intro x hx
    obtain ⟨y, hy⟩ := surj (V.subtype.rangeRestrict ⟨x, hx⟩)
    have e : y.val = x := (RingHom.congr_fun incl y).symm.trans (congrArg Subtype.val hy)
    exact e ▸ y.property

/-- The normalization of the parameter line in the curve function field,
as an actual subring of that field. -/
noncomputable abbrev lineNormalization (K L : Type*) [Field K] [Field L] [Algebra (Polynomial K) L] :
    Subring L := (integralClosure (Polynomial K) L).toSubring

/-- A place above zero is the local ring at a nonzero prime of the normalization
of the parameter line. -/
theorem exists_normalized_center {K L : Type*} [Field K] [Field L]
    [Algebra (Polynomial K) L] [Algebra (FractionRing (Polynomial K)) L]
    [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
    [FiniteDimensional (FractionRing (Polynomial K)) L]
    [Algebra.IsSeparable (FractionRing (Polynomial K)) L]
    (V : ValuationSubring L) (hregular : ∀ a : Polynomial K, algebraMap _ L a ∈ V)
    (hzero : algebraMap (Polynomial K) L Polynomial.X ∈ V.nonunits) :
    ∃ (P : Ideal (lineNormalization K L)) (_ : P.IsPrime), P ≠ ⊥ ∧
      (LocalSubring.ofPrime (lineNormalization K L) P).toSubring = V.toSubring := by
  let B := (integralClosure (Polynomial K) L).toSubring
  have : IsDedekindDomain B := inferInstanceAs (IsDedekindDomain (integralClosure (Polynomial K) L))
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension
    (Polynomial K) (FractionRing (Polynomial K)) L (integralClosure (Polynomial K) L)
  have : IsIntegrallyClosedIn V.toSubring L := inferInstanceAs (IsIntegrallyClosedIn V L)
  have hBV : B ≤ V.toSubring := Subring.integralClosure_le_iff.mpr hregular
  let P := (IsLocalRing.maximalIdeal V).comap (Subring.inclusion hBV)
  let t : B := ⟨algebraMap (Polynomial K) L Polynomial.X, isIntegral_algebraMap⟩
  have hne : P ≠ ⊥ := by
    have hm : t ∈ P := V.coe_mem_nonunits_iff.mp hzero
    have h : t ≠ 0 := by
      apply mt (congrArg Subtype.val)
      change algebraMap (Polynomial K) L Polynomial.X ≠ 0
      rw [IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K)) L]
      let j := algebraMap (FractionRing (Polynomial K)) L
      let k := algebraMap (Polynomial K) (FractionRing (Polynomial K))
      intro hz
      exact Polynomial.X_ne_zero ((IsFractionRing.injective _ _ : Function.Injective k)
        ((j.injective (hz.trans (map_zero j).symm)).trans (map_zero k).symm))
    exact fun e => h (show t ∈ (⊥ : Ideal B) from e ▸ hm)
  exact ⟨P, inferInstance, hne, valuation_eq_localization B V hBV hne⟩

/-- Above `t = 0` a valuation ring of a finite separable one-variable function
field is discrete. The regularity of any outputs in the ring is preserved. -/
theorem discrete_place_over_parameter {K L : Type*} [Field K] [Field L]
    [Algebra (Polynomial K) L] [Algebra (FractionRing (Polynomial K)) L]
    [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
    [FiniteDimensional (FractionRing (Polynomial K)) L]
    [Algebra.IsSeparable (FractionRing (Polynomial K)) L]
    (V : ValuationSubring L) (hregular : ∀ a : Polynomial K, algebraMap _ L a ∈ V)
    (hzero : algebraMap (Polynomial K) L Polynomial.X ∈ V.nonunits) :
    IsDiscreteValuationRing V := by
  obtain ⟨P, _, hne, eq⟩ := exists_normalized_center V hregular hzero
  change IsDiscreteValuationRing V.toSubring
  rw [← eq]
  have : IsDedekindDomain (lineNormalization K L) :=
    inferInstanceAs (IsDedekindDomain (integralClosure (Polynomial K) L))
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hne _

end Branch

end BorderVNP
end Computability
end OAI
