import OAI.LinearAlgebra.SpectralBooks.SiteWireClasses
import OAI.LinearAlgebra.SpectralBooks.BinaryWirePlacement
import OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal

/-! # Matrix multiplication wires at an injective placement

All three edge prices and the full diagonal price are evaluated at the same
three-site spectral point. This converts the binary metric-price law of a
spectral space into wire evaluations in every positive dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical NNReal
noncomputable section

section

open SiteTensor

/-- When every site is occupied, the masked diagonal is the full diagonal. -/
theorem SiteTensor.ofRaw_maskDiagonal_univ {I F : Type*} [Fintype I] [Field F]
    (α : Type) [Fintype α] :
    ofRaw (Raw.maskDiagonal F (Finset.univ : Finset I) α) = ofRaw (Raw.diagonal I F α) := by
  let e (i : I) : MaskLeg Finset.univ α i ≃ α :=
    { toFun := fun g => g (Finset.mem_univ i)
      invFun := fun a _ => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Raw.diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply propext
  constructor
  · rintro rfl
    rfl
  · exact fun h => funext (fun i => funext (fun _ => congrFun h i))

section
variable {F X : Type*} [Field F] [PseudoMetricSpace X]

private theorem wire_scale {P : SpectralPlacementPrices F X} {e : Fin 3 ↪ X}
    {φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) F → _ → Prop)} {c : ℝ}
    (hm : ∀ S : Finset (Fin 3), S.Nonempty → P.diagonal (S.map e) =
      c * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal F S (Fin 2))) : ℝ)) :
    P.diagonal (Finset.univ.image e) = c := by
  have h := hm Finset.univ Finset.univ_nonempty
  have he := map_natCast (normalizedSpectrum.toRingHom φ) 2
  change φ.val (2 : TensorClass.{0} (Fin 3) F) = 2 at he
  rw [ofRaw_maskDiagonal_univ, ofRaw_diagonal_fin_eq_natCast] at h
  simpa [Finset.map_eq_image, he, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- The three binary wire distances in a spectral placement provide the
normalized functional for all positive matrix multiplication wire sizes. -/
def SpectralPlacementPrices.placedWires (P : SpectralPlacementPrices F X) (e : Fin 3 ↪ X) :
    PlacedWires F e (P.diagonal (Finset.univ.image e)) := by
  apply Classical.choice
  let d := P.diagonal (Finset.univ.image e)
  obtain ⟨φ, c, _, hm⟩ := P.exists_point_diagonal_map e
  have hdc : d = c := wire_scale hm
  have hpair (i j : Fin 3) : d * Real.logb 2
      (φ.val (ofRaw (Raw.maskDiagonal F {i,j} (Fin 2))) : ℝ) = dist (e i) (e j) := by
    rw [hdc, ← hm {i,j} (by simp), Finset.map_insert, Finset.map_singleton, P.diagonal_pair]
  refine ⟨PlacedWires.ofBinary (rankFunctionalOfSpectrum φ) (P.diagonal_nonneg _) ?_ ?_ ?_⟩
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire12 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire12]
    exact hpair 0 1
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire23 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire23]
    exact hpair 1 2
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire31 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire31]
    exact hpair 2 0

end
end

end

end SpectralBooks
end LinearAlgebra
end OAI
