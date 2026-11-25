import OAI.LinearAlgebra.FiniteFourier.TransvectionLayer

/-! # The singleton and constant frequency in the dyadic prime transform

With orbit length `m = p - 1`, first add the orbit sum to the singleton.
Multiplying the constant frequency by `-p/m` and adding the new singleton then
gives the binomial constant coefficient. All other frequencies only need scaling.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

open Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The diagonal between the two row additions. -/
def dyadicPrimeScales (z : Fin m) (hm : IsUnit (m:R)) (hp : IsUnit ((m:R) + 1))
    (d : Fin m → Rˣ) : Option (Fin m) → Rˣ
  | none => 1
  | some j => if j = z then -(hp.unit * hm.unit⁻¹) else hm.unit⁻¹ * d j

/-- The seven-slot conversion on the Fourier registers, including the singleton. -/
def dyadicPrimeMix (z : Fin m) (hm : IsUnit (m:R)) (hp : IsUnit ((m:R) + 1))
    (d : Fin m → Rˣ) : Matrix (Option (Fin m)) (Option (Fin m)) R :=
  transvection (some z) none 1 *
    (diagonal (fun i => (dyadicPrimeScales z hm hp d i : R)) *
      transvection none (some z) 1)

private theorem dyadicShearPair {I : Type} [Fintype I] [DecidableEq I]
    {i j : I} (hij : i ≠ j) :
    let T := transvection i j (1:R)
    LayerWord 3 T ∧ LayerWord 3 T⁻¹ := by
  have hinv : (transvection i j (1:R))⁻¹ = transvection i j (-1) :=
    Matrix.inv_eq_left_inv (by rw [transvection_mul_transvection_same _ _ hij,
      neg_add_cancel, transvection_zero])
  exact ⟨layerWord_transvection_unit hij 1,
    hinv ▸ layerWord_transvection_unit hij (-1)⟩

/-- Both directions of the singleton conversion have bounded depth independently
of the prime. -/
theorem dyadicPrimeMix_layerWords (z : Fin m) (hm : IsUnit (m:R))
    (hp : IsUnit ((m:R) + 1)) (d : Fin m → Rˣ) :
    LayerWord 7 (dyadicPrimeMix z hm hp d) ∧ LayerWord 7 (dyadicPrimeMix z hm hp d)⁻¹ := by
  let s := dyadicPrimeScales z hm hp d
  let D := diagonal (fun i => (s i : R))
  have hD : LayerWord 1 D :=
    layerWord_of_layer (layerMatrix_diagonal_units fun i => (s i).isUnit)
  have hE : D⁻¹ = diagonal fun i => (↑(s i)⁻¹ : R) :=
    Matrix.inv_eq_left_inv (by simp [D, diagonal_mul_diagonal])
  have hDi : LayerWord 1 D⁻¹ := hE ▸
    layerWord_of_layer (layerMatrix_diagonal_units fun i => (s i)⁻¹.isUnit)
  have hA := dyadicShearPair (R := R) (Option.some_ne_none z)
  have hB := dyadicShearPair (R := R) (Option.some_ne_none z).symm
  refine ⟨layerWord_mul hA.1 (layerWord_mul hD hB.1), ?_⟩
  unfold dyadicPrimeMix
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  exact layerWord_mul (layerWord_mul hB.2 hDi) hA.2

end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
