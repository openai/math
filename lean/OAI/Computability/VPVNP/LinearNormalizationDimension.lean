import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Number of variables in an integral polynomial normalization

In a polynomial ring over a field, an injective integral normalization has
as many coordinates as the ambient polynomial ring has variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

/-- Integrality of an algebra homomorphism makes each target element integral
over its image subalgebra. -/
theorem isIntegral_range {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) (hf : f.IsIntegral)
    (p : B) : IsIntegral f.range p :=
  RingHom.IsIntegralElem.of_comp
    (f := f.rangeRestrict.toRingHom) (g := algebraMap f.range B) (hf p)

/-- Integrality over the image characterizes an integral homomorphism. -/
theorem isIntegral_iff_range {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    f.IsIntegral ↔ ∀ p : B, IsIntegral f.range p := by
  refine ⟨isIntegral_range f, fun h ↦ ?_⟩
  exact RingHom.IsIntegral.trans f.rangeRestrict.toRingHom (algebraMap f.range B)
    (RingHom.isIntegral_of_surjective _ f.rangeRestrict_surjective) h

/-- The image of the source variables is a transcendence basis of the target,
so the two polynomial rings have the same number of variables. -/
theorem numVars_eq_of_integral_injective {K : Type*} [Field K] {s m : ℕ}
    (f : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K)
    (hf : Function.Injective f) (hi : f.IsIntegral) : s = m := by
  let P := MvPolynomial (Fin s) K
  let Q := MvPolynomial (Fin m) K
  let : Algebra P Q := f.toRingHom.toAlgebra
  let : IsScalarTower K P Q := .of_algebraMap_eq fun k ↦ (f.commutes k).symm
  let : FaithfulSMul P Q := (faithfulSMul_iff_algebraMap_injective P Q).mpr hf
  let : Algebra.IsIntegral P Q := ⟨hi⟩
  have h := (IsTranscendenceBasis.mvPolynomial (Fin s) K).algebraMap_comp (A := Q)
  simpa using h.cardinalMk_eq (IsTranscendenceBasis.mvPolynomial (Fin m) K)

end LinearNormalization

end VPVNP
end Computability
end OAI
