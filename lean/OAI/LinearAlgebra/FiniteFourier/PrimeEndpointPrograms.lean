import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointPairCost
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointLabelCoordinates

/-! # The shared endpoint programs on the physical row

Both endpoint transforms use the auxiliary spaces fixed at their label. The
auxiliary chirp is attached to the ordinary side of each transform, so each
program is independent of the selected distinguished digit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open scoped Classical
set_option synthInstance.maxSize 512

variable {ℓ f : ℕ} [Fact ℓ.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod ℓ) E]
  [FiniteDimensional (ZMod ℓ) E] {J U : Type} [Fintype J] [Fintype U]
  {p q : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ)} {H : Submodule (ZMod ℓ) E}
  {K : Type*} [CommRing K] {ζ : K}

private abbrev Residual (J : Type) (f : ℕ) (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) :=
  EndpointDigitPairs (Fin f) J (ZMod ℓ) × ((Fin f → P.C) × (Fin f → Q.C))

private def auxPhase (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H)
    (i : PrimeCommonPair ℓ f (Module.finrank (ZMod ℓ) H) × Residual J f P Q) : K :=
  digitPhase hζ (-↑(a⁻¹) * endpointLabelCoordinateAux P Q (Module.finBasis (ZMod ℓ) H).equivFun i)

/-- The initial endpoint, with its physical-to-chart permutation and input chirp. -/
def primeSourceEndpoint (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C] :=
  let e := endpointLabelFinChart (C := Fin f) (J := J) P Q
  Matrix.reindex e e (endpointPartial (endpointPairFourier (f := f) (h := Module.finrank (ZMod ℓ) H) hζ a) (Residual J f P Q) *
    Matrix.diagonal (auxPhase (f := f) (J := J) hζ a P Q))

/-- The final endpoint, with the auxiliary chirp on the output coordinates. -/
def primeTargetEndpoint (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C] :=
  let e := endpointLabelFinChart (C := Fin f) (J := J) P Q
  Matrix.reindex e e (Matrix.diagonal (auxPhase (f := f) (J := J) hζ a P Q) *
    endpointPartial (endpointPairFourier (f := f) (h := Module.finrank (ZMod ℓ) H) hζ a) (Residual J f P Q))

private theorem endpoint_program (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C]
    (hA : 0 < 2 * (Fintype.card J + Fintype.card U)) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((2*(Fintype.card J + Fintype.card U)-1)*f)) ζ
      (endpointPartial (endpointPairFourier (f := f) (h := Module.finrank (ZMod ℓ) H) hζ a)
        (Residual J f P Q)) 0 (2*Module.finrank (ZMod ℓ) H) := by
  let e := endpointLabelFinChart (C := Fin f) (J := J) P Q
  apply primeTemplate_endpointPairFourier_of_chart hA hζ a _ _ e.symm
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card]
  rw [← pow_add]
  congr 1
  ring

/-- The shared source program uses one oracle call on each active axis of each half. -/
theorem primeSourceEndpoint_program (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C]
    (hA : 0 < 2 * (Fintype.card J + Fintype.card U)) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((2*(Fintype.card J + Fintype.card U)-1)*f)) ζ
      (primeSourceEndpoint (J := J) (f := f) hζ a P Q) 0 (2*Module.finrank (ZMod ℓ) H) := by
  let e := endpointLabelFinChart (C := Fin f) (J := J) P Q
  have pr := endpoint_program (f := f) hζ a P Q hA
  apply PrimeTemplateProgram.reindex (eo := e) (ei := e)
  convert pr.diagonal (fun _ => 1) (auxPhase (f := f) (J := J) hζ a P Q) using 1
  ext o i
  simp [Matrix.mul_diagonal, mul_comm]

/-- The shared target program uses the same budget, with its free diagonal following the transform. -/
theorem primeTargetEndpoint_program (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C]
    (hA : 0 < 2 * (Fintype.card J + Fintype.card U)) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((2*(Fintype.card J + Fintype.card U)-1)*f)) ζ
      (primeTargetEndpoint (J := J) (f := f) hζ a P Q) 0 (2*Module.finrank (ZMod ℓ) H) := by
  let e := endpointLabelFinChart (C := Fin f) (J := J) P Q
  have pr := endpoint_program (f := f) hζ a P Q hA
  apply PrimeTemplateProgram.reindex (eo := e) (ei := e)
  convert pr.diagonal (auxPhase (f := f) (J := J) hζ a P Q) (fun _ => 1) using 1
  ext o i
  simp [Matrix.diagonal_mul]

end

end FiniteFourier
end LinearAlgebra
end OAI
