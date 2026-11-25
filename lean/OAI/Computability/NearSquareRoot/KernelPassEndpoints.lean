import OAI.Computability.NearSquareRoot.KernelPassEndpointPair
import OAI.Computability.NearSquareRoot.KernelEndpointCross
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointPrograms
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumEquiv

/-! # Physical source and target passes of a binary geometric rectangle

In one column the two halves of the shared subspace give a partial Walsh
transform. The auxiliary character is evaluated at the input of the source
pass and at the output of the target pass. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

noncomputable section
open OAI.LinearAlgebra.FiniteFourier KernelNormalization Matrix Module

variable {A : ℕ} {J U : Type} [Fintype J] [Fintype U]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    {p q : E ≃ₗ[ZMod 2] ZMod 2 × (U → ZMod 2)} {H : Submodule (ZMod 2) E}
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C]

private abbrev Residual := EndpointLabelResidualIndex (Fin 1) J (ZMod 2) P.C Q.C

private def readChart
    (e : Bits A ≃ₗ[ZMod 2] PrimeSpectrumDigits (Fin 1 × (J ⊕ U)) 2) :
    Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 (finrank (ZMod 2) H) × Residual (J := J) P Q :=
  e.trans (KernelEndpointCross.linear
    (KernelEndpointCross.endpointLabelAddChart (C := Fin 1) (J := J) P Q)).symm

set_option synthInstance.maxSize 512 in
/-- Each normalized physical endpoint uses at most two child calls per
shared basis direction, for every binary linear encoding of the row address. -/
theorem Realizes.geometricEndpoints
    (e : Bits A ≃ₗ[ZMod 2] PrimeSpectrumDigits (Fin 1 × (J ⊕ U)) 2) :
    Realizes (2 * finrank (ZMod 2) H)
      (((2 : ℂ)⁻¹ ^ finrank (ZMod 2) H • primeSourceEndpoint (f := 1) (J := J)
        binaryRoot (1 : (ZMod 2)ˣ) P Q).submatrix e e) ∧
    Realizes (2 * finrank (ZMod 2) H)
      (((2 : ℂ)⁻¹ ^ finrank (ZMod 2) H • primeTargetEndpoint (f := 1) (J := J)
        binaryRoot (1 : (ZMod 2)ˣ) P Q).submatrix e e) := by
  classical
  let c := readChart P Q e
  let F := endpointPartial
    (endpointPairFourier (f := 1) (h := finrank (ZMod 2) H) binaryRoot (1 : (ZMod 2)ˣ))
    (Residual (J := J) P Q)
  let z : ℂ := (2 : ℂ)⁻¹ ^ finrank (ZMod 2) H
  let phase := fun t => -↑((1 : (ZMod 2)ˣ)⁻¹) *
    endpointLabelCoordinateAux P Q (finBasis (ZMod 2) H).equivFun (J := J) (C := Fin 1) t
  let d := diagonal (fun t => character (phase t))
  let l := endpointLabelFinChart (C := Fin 1) (J := J) P Q
  have hs : primeSourceEndpoint (f := 1) (J := J) binaryRoot (1 : (ZMod 2)ˣ) P Q =
      reindex l l (F * d) := rfl
  have ht : primeTargetEndpoint (f := 1) (J := J) binaryRoot (1 : (ZMod 2)ˣ) P Q =
      reindex l l (d * F) := rfl
  have hd := Realizes.sign (fun x => phase (c x))
  have hw := Realizes.endpointPair c
  have hfirst := hw.mul hd
  have hlast := hd.mul hw
  rw [Nat.add_zero] at hfirst
  rw [Nat.zero_add] at hlast
  rw [hs, ht]
  constructor
  · convert hfirst using 1
    ext y x
    change z * (F * d) (c y) (c x) = ((z • F).submatrix c c *
      diagonal (fun t => character (phase (c t)))) y x
    simp only [d, mul_diagonal, submatrix_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  · convert hlast using 1
    ext y x
    change z * (d * F) (c y) (c x) = (diagonal (fun t => character (phase (c t))) *
      (z • F).submatrix c c) y x
    simp only [d, diagonal_mul, submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    exact mul_left_comm _ _ _

end

end KernelPass

end NearSquareRoot
end Computability
end OAI
