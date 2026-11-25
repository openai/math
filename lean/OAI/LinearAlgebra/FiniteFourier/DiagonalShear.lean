import OAI.LinearAlgebra.FiniteFourier.TransvectionLayer

/-! # Disjoint scalar shears on two arrays

Each coordinate pair has its own scalar transvection. The block-diagonal word
performs all pairs simultaneously, including the identity on pairs with zero coefficient.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix

variable {K : Type*} [CommRing K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Group the first and second registers of each coordinate pair into two arrays. -/
private def pairArrays (I : Type) : (Σ _ : I, Fin 2) ≃ I ⊕ I where
  toFun p := if p.2 = 0 then .inl p.1 else .inr p.1
  invFun := Sum.elim (fun i => ⟨i, 0⟩) (fun i => ⟨i, 1⟩)
  left_inv := by rintro ⟨i, k⟩; fin_cases k <;> rfl
  right_inv := by rintro (i | i) <;> rfl

omit [Fintype I] in
private theorem pairArrays_transvections (d : I → K) :
    (blockDiagonal' fun i => transvection (0 : Fin 2) 1 (d i)).submatrix
      (pairArrays I).symm (pairArrays I).symm =
    fromBlocks 1 (diagonal d) 0 1 := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [submatrix, pairArrays, blockDiagonal'_apply, h, transvection, Matrix.single_apply,
      Matrix.one_apply, fromBlocks, diagonal]

/-- Applying a scalar shear word to each pair synchronously gives a diagonal addition. -/
theorem layerWord_diagShear_upper_of_pairs {d : ℕ} (c : I → K)
    (h : ∀ i, LayerWord d (transvection (0 : Fin 2) 1 (c i))) :
    LayerWord d (fromBlocks 1 (diagonal c) 0 1) := by
  rw [← pairArrays_transvections]
  exact (layerWord_blocks h).relabel _

/-- All scalar shears execute in three synchronized slot pairs. -/
theorem layerWord_diagShear_upper {K : Type*} [Field K] (d : I → K) :
    LayerWord 3 (fromBlocks 1 (diagonal d) 0 1) := by
  exact layerWord_diagShear_upper_of_pairs d fun i => layerWord_transvection (by decide) (d i)

/-- The simultaneous unit additions use one shear layer. -/
theorem layerMatrix_diagUnit_upper :
    LayerMatrix .shear (fromBlocks 1 (1 : Matrix I I K) 0 1) := by
  have h := (LayerMatrix.blocks (fun _ : I =>
    LayerMatrix.unitTransvection (K := K) (by decide : (0 : Fin 2) ≠ 1))).relabel (pairArrays I)
  simpa only [pairArrays_transvections, Matrix.diagonal_one] using h

/-- Exchanging the two array labels reverses the direction of an additive update. -/
theorem LayerWord.swapShear {d : ℕ} {A : Matrix I J K}
    (h : LayerWord d (fromBlocks 1 0 A 1)) :
    LayerWord d (fromBlocks 1 A 0 1) := by
  convert h.relabel (Equiv.sumComm J I) using 1
  ext (i | i) (j | j) <;> rfl

theorem layerWord_diagShear_lower {K : Type*} [Field K] (d : I → K) :
    LayerWord 3 (fromBlocks 1 0 (diagonal d) 1) := by
  convert (layerWord_diagShear_upper d).relabel (Equiv.sumComm I I) using 1
  ext (i | i) (j | j) <;> rfl

/-- Diagonal additions over a ring where each scalar splits as a sum of units. -/
theorem layerWord_diagShear_lower_of_unit_split
    (hs : ∀ s : K, ∃ t : K, IsUnit t ∧ IsUnit (s-t)) (d : I → K) :
    LayerWord 6 (fromBlocks 1 0 (diagonal d) 1) := by
  have h := layerWord_diagShear_upper_of_pairs d fun i =>
    layerWord_transvection_of_unit_split hs (by decide) (d i)
  convert h.relabel (Equiv.sumComm I I) using 1
  ext (i | i) (j | j) <;> rfl

theorem layerMatrix_diagUnit_lower :
    LayerMatrix .shear (fromBlocks 1 0 (1 : Matrix I I K) 1) := by
  convert (layerMatrix_diagUnit_upper (K := K) (I := I)).relabel (Equiv.sumComm I I) using 1
  ext (i | i) (j | j) <;> rfl

/-- The signed interchange sends the two arrays `(x, y)` to `(-y, x)`. -/
theorem layerMatrix_signedSwap :
    LayerMatrix .monomial (fromBlocks 0 (-1 : Matrix I I K) 1 0) := by
  let ε : I ⊕ I → Kˣ := Sum.elim (fun _ => -1) (fun _ => 1)
  have h : fromBlocks 0 (-1 : Matrix I I K) 1 0 =
      (fun i j => if (Equiv.sumComm I I) i = j then (ε i : K) else 0) := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;>
      simp [fromBlocks, hij, ε]
  rw [h]
  exact LayerMatrix.monomial (Equiv.sumComm I I) ε

theorem layerWord_signedSwap :
    LayerWord 1 (fromBlocks 0 (-1 : Matrix I I K) 1 0) :=
  layerWord_of_layer layerMatrix_signedSwap

end

end

end FiniteFourier
end LinearAlgebra
end OAI
