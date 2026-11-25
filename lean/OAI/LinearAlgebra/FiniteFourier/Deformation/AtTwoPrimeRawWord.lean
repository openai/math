import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeRawFourier
import OAI.LinearAlgebra.FiniteFourier.AtTwoFourierInverse

/-! # Synchronized words on the two signed Fourier rows

The two orbit transforms run at the same depth, fixing the zero address.
For a transform with occupied workspace, give each orbit its own copy of
that workspace. Relabeling places all restored workspace after the active axis.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix
open scoped Kronecker

variable {R : Type*} [CommRing R] {m d : ℕ} {D : Matrix (Fin m) (Fin m) R}

/-- Apply a word to both orbit rows, fixing the zero address, at the same depth. -/
theorem layerWord_atTwoRawTransform (h : LayerWord d D) : LayerWord d (atTwoRawTransform D) :=
  layerWord_parallel (layerWord_one _) (layerWord_tensor (layerWord_one _) h)

/-- Lift a word with arbitrary occupied workspace to both orbit rows. Each
orbit restores its own workspace registers. -/
theorem layerWord_atTwoRawTransform_occupied {W : Type} [Fintype W] [DecidableEq W]
    (h : LayerWord d (fromBlocks D 0 0 (1 : Matrix W W R))) :
    LayerWord d (fromBlocks (atTwoRawTransform D) 0 0 (1 : Matrix (Bool × W) (Bool × W) R)) := by
  let e : PUnit.{1} ⊕ (Bool × (Fin m ⊕ W)) ≃ AtTwoRawIndex m ⊕ (Bool × W) :=
    ((Equiv.refl PUnit).sumCongr (Equiv.prodSumDistrib Bool (Fin m) W)).trans
      (Equiv.sumAssoc _ _ _).symm
  have hp := layerWord_parallel (layerWord_one (I := PUnit.{1}) d)
    (layerWord_tensor (layerWord_one (I := Bool) d) h)
  convert hp.relabel e using 1
  ext i j
  rcases i with (i | ⟨a,i⟩) | ⟨a,i⟩ <;> rcases j with (j | ⟨b,j⟩) | ⟨b,j⟩ <;>
    simp [atTwoRawTransform, fromBlocks, submatrix, e, Equiv.prodSumDistrib, Equiv.sumAssoc,
      one_apply, kroneckerMap_apply, Prod.ext_iff, ite_mul]
  split_ifs <;> simp_all


private theorem occupiedWord_unit_scale {I W : Type} [Fintype I] [Fintype W]
    [DecidableEq I] [DecidableEq W] {A : Matrix I I R} (v : Rˣ)
    (h : OccupiedWord W d A) : OccupiedWord W (1+d) ((v:R) • A) := by
  have hS : LayerWord 1 (diagonal fun _ : I => (v:R)) :=
    layerWord_of_layer (layerMatrix_diagonal_units fun _ => v.isUnit)
  have hSA := hS.occupied.mul h
  convert hSA using 2
  ext i j
  simp [diagonal_mul, smul_eq_mul]

/-- From one positive Fourier word obtain analysis (positive sign and division
by the row length) and synthesis (negative sign) on the raw prime coordinates.
The bound includes unit rescalings and frequency reversal. -/
theorem occupiedWord_atTwoRawFourier_pair {W : Type} [Fintype W] [DecidableEq W]
    [NeZero m] (u : Rˣ) (hu : u^m = 1) (hm : IsUnit (m : R))
    (hs : Pairwise fun i j : Fin m => IsUnit ((u:R)^i.val - (u:R)^j.val))
    (hF : OccupiedWord W d (geometricMatrix m (u:R))) :
    OccupiedWord (Bool × W) (1+d)
      (atTwoRawTransform ((↑hm.unit⁻¹ : R) • dftMatrix m (u:R))) ∧
    OccupiedWord (Bool × W) (1+(1+d)) (atTwoRawTransform (dftMatrix m (↑u⁻¹ : R))) := by
  have hA := occupiedWord_unit_scale hm.unit⁻¹ hF
  rw [geometricMatrix_eq_dftMatrix] at hA
  have hS := occupiedWord_inverse_geometricMatrix_of_separated u hu hm hs hF
  rw [geometricMatrix_eq_dftMatrix, inv_dftMatrix_of_unit_differences u hu hm hs] at hS
  have hN := occupiedWord_unit_scale hm.unit hS
  rw [smul_smul, Units.mul_inv, one_smul] at hN
  exact ⟨layerWord_atTwoRawTransform_occupied hA, layerWord_atTwoRawTransform_occupied hN⟩

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
