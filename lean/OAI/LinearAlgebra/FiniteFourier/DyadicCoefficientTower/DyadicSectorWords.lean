import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicFourierAxis
import OAI.LinearAlgebra.FiniteFourier.DyadicWordTransport
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformation
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.JetOccupiedGridCircuit
import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs

/-! # Forward and inverse tensor Fourier circuits within each dyadic sector

An active axis contributes the Fourier transform on the nonzero residue
orbit. Both endpoint matrices are mapped from the protected coefficient
order into the long jet. All axes of a sector share the occupied registers,
including when the sector is empty.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Matrix ConvolutionGrid Deformation.Dyadic

variable {η : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B}
  {L : Finset ℕ} (T : DyadicCoefficientTower D L)

private theorem map_grid_columns {σ R K : Type*} [Fintype σ] [CommRing R] [CommRing K]
    {P : σ → Type*} (f : R →+* K) (v : ∀ i, Matrix (P i) (P i) R) :
    (gridTensor v).map f = columns (fun i => (v i).map f) := by
  ext x y
  simp [gridTensor, columns]

/-- For the selected unit roots, the true evaluation and interpolation
operators on the long jets both use the same explicit base-ring budget. -/
theorem sectorFourierCircuits (S : Finset D.packing.axes) (w : D.packing.axes → T.Orderˣ)
    (hsep : ∀ i : D.packing.axes, Pairwise fun j k : Fin (i.val-1) =>
      IsUnit ((w i : T.Order)^j.val - (w i : T.Order)^k.val))
    {H s : ℕ} (hH : 0 < H) (hs : 2*(listCyclotomicDegree GaussianRationals D.pool B)*H ≤ s)
    {β C : ℝ} (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    let m := fun i : S => i.val.val-1
    let ζ := fun (i : S) (j : Fin (m i)) => (w i.val : T.Order)^j.val
    let e := listCyclotomicDegree GaussianRationals D.pool B
    let f := algebraMap T.Order (JetQuotient T.modulus H)
    let φ := algebraMap (protectedRationals L) (protectedGaussian L)
    let W := Fintype.card (Address m)
    let cost := occupiedGridJetCost β C 14 (6400*(1+Nat.clog 2 (2+B))) W e H s
    JetMatrixCircuit φ (protectedGaussianI L) T.modulus e H ((evaluation m ζ).map f) cost ∧
      JetMatrixCircuit φ (protectedGaussianI L) T.modulus e H ((interpolation m ζ).map f) cost := by
  classical
  intro m ζ e f φ W cost
  let P (i : S) := Fin (m i)
  have hin (i : S) := D.axis_properties T.width i.val.property
  have ha (i : S) : 2 ≤ m i := by
    dsimp [m]
    have := (hin i).2.1
    omega
  have hwords (dir : Bool) (i : S) :
      let V := vandermonde (ζ i)
      let A := if dir then V else V⁻¹
      OccupiedWord (Fin (13*m i)) (6400*(1+Nat.clog 2 (2+B))) (A.map f) := by
    intro V A
    have heq : V = dftMatrix (m i) (w i.val : T.Order) := by
      ext j k
      simp [V, ζ, vandermonde_apply, dftMatrix, pow_mul]
    have hB : m i ≤ B := (Nat.sub_le ..).trans (hin i).2.2.1
    have hw := T.fourierWord (RingHom.id _) (by have := ha i; omega : 0 < m i) hB
      T.split (w i.val).isUnit (hsep i.val) (A := A) (by
        dsimp only [A]
        cases dir <;> simp [heq])
    exact hw.mapCoefficients f
  have hdir (dir : Bool) :
      let A := fun i : S => if dir then vandermonde (ζ i) else (vandermonde (ζ i))⁻¹
      JetMatrixCircuit φ (protectedGaussianI L) T.modulus e H ((gridTensor A).map f) cost := by
    intro A
    rw [map_grid_columns]
    apply occupiedGridMatrixCircuit (X := P) (W := fun i => Fin (13*m i))
      _ (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) (by decide : 0 < 14)
      (by simpa [P] using ha) (by simp [P, Nat.mul_comm])
    · intro i
      exact hwords dir i
    · exact T.jets hH
    · exact protectedGaussian_coordinates L
    · exact T.monic
    · exact T.degree_eq
    · exact degree_pos (D := D)
    · exact hH
    · exact hs
    · exact ht.shearTensorBound _
    · exact hβ
    · exact hC
  exact ⟨by simpa [evaluation] using hdir true, by simpa [interpolation] using hdir false⟩

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
