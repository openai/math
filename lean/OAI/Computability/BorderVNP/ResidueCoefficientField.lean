import Mathlib.RingTheory.Teichmuller
import Mathlib.FieldTheory.Finite.Basic

/-! # The coefficient field of a completed branch

Section 10.1 works in equal positive characteristic with a finite residue
field. The inverse Frobenius lifts in the residue field define compatible
lifts through every power of the maximal ideal. Their limit is a ring
section of reduction, which lifts precisely the roots of `T ^ |κ| - T`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

variable {R : Type*} [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
  [CharP R p] [CharP (R ⧸ I) p] [IsAdicComplete I R]

private noncomputable def perfectionReduction : Perfection R p ≃+* Perfection (R ⧸ I) p :=
  RingEquiv.ofBijective (Perfection.map p (Ideal.Quotient.mk I))
    (Perfection.quotientMulEquiv p I).bijective

/-- Coherent Frobenius lifts in the complete ring give the coefficient-field section. -/
noncomputable def coefficientSection [PerfectRing (R ⧸ I) p] : (R ⧸ I) →+* R :=
  (Perfection.coeff R p 0).comp <| (perfectionReduction I p).symm.toRingHom.comp
    (Perfection.lift p _ _ (RingHom.id (R ⧸ I)))

/-- Reduction of a coefficient representative returns the prescribed residue. -/
theorem reduction_coefficientSection [PerfectRing (R ⧸ I) p] (a : R ⧸ I) :
    Ideal.Quotient.mk I (coefficientSection I p a) = a := by
  let x := Perfection.lift p (R ⧸ I) (R ⧸ I) (RingHom.id _) a
  exact congrArg (Perfection.coeff (R ⧸ I) p 0) ((perfectionReduction I p).apply_symm_apply x)

/-- In the finite residue field case these representatives are roots of the
same polynomial `T ^ |κ| - T` upstairs. -/
theorem coefficientSection_pow_card [I.IsMaximal] [Fintype (R ⧸ I)] (a : R ⧸ I) :
    coefficientSection I p a ^ Fintype.card (R ⧸ I) = coefficientSection I p a := by
  let := Ideal.Quotient.field I
  rw [← map_pow]
  exact congrArg (coefficientSection I p) (FiniteField.pow_card a)

end Residue

end BorderVNP
end Computability
end OAI
