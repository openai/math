import OAI.Computability.BorderVNP.DecisionDeformationFractionField

/-!
# The rational parameter field on a prime component

For the quotient domain `A` of the deformation component, evaluate the
parameter polynomial at the image of `t`, then pass to `Frac(A)`. Dominance
makes this map injective and gives the embedding of `K(t)` into the same
fraction field. The towers below let the graph, point and valuation-ring maps
all act on this one field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Decision

/-- The scalar towers on the component and its fraction field, including the
identity of the deformation parameter in the component ring. -/
theorem component_scalar_towers (K : Type*) {A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] (a : A) (ha : Function.Injective (Polynomial.aeval (R := K) a)) :
    letI := (Polynomial.aeval (R := K) a).toRingHom.toAlgebra
    letI := (parameterFractionMap K a ha).toAlgebra
    IsScalarTower (Polynomial K) A (FractionRing A) ∧
      IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) (FractionRing A) ∧
      IsScalarTower K (FractionRing (Polynomial K)) (FractionRing A) ∧
      IsScalarTower K (Polynomial K) A ∧ a = algebraMap (Polynomial K) A Polynomial.X := by
  let := (Polynomial.aeval (R := K) a).toRingHom.toAlgebra
  let := (parameterFractionMap K a ha).toAlgebra
  have hA : IsScalarTower (Polynomial K) A (FractionRing A) := inferInstance
  have hT : IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) (FractionRing A) :=
    .of_algebraMap_eq fun p => (parameterFractionMap_polynomial K a ha p).symm
  have hKA : IsScalarTower K (Polynomial K) A := .of_algebraMap_eq fun z => (Polynomial.aeval_C a z).symm
  have : IsScalarTower K (Polynomial K) (FractionRing A) :=
    IsScalarTower.to₁₂₄ K (Polynomial K) A (FractionRing A)
  exact ⟨hA, hT, IsScalarTower.to₁₃₄ K (Polynomial K) _ _, hKA, (Polynomial.aeval_X a).symm⟩

end Branch

end BorderVNP
end Computability
end OAI
