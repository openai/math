import OAI.LinearAlgebra.FiniteFourier.OccupiedAxes
import OAI.LinearAlgebra.FiniteFourier.OccupiedWord

/-! # Parallel axis calls on a common occupied workspace

Each fiber receives its own share of the workspace during an axis call.
The workspace is restored at the end of the call and reused on the next axis.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Kronecker

variable {K : Type*} [CommSemiring K] {I W J V : Type}
  [Fintype I] [Fintype W] [Fintype J] [Fintype V]
  [DecidableEq I] [DecidableEq W] [DecidableEq J] [DecidableEq V]

/-- Apply one copy of the word on each fiber and enlarge the union of the
individual workspaces to any common workspace that can accommodate it. -/
theorem LayerWord.parallelOccupiedCopies {d : ℕ} {A : Matrix I I K}
    (h : LayerWord d (fromBlocks A 0 0 (1 : Matrix W W K)))
    (hV : Fintype.card (W × J) ≤ Fintype.card V) :
    LayerWord d (fromBlocks (blockDiagonal fun _ : J => A) 0 0 (1 : Matrix V V K)) := by
  apply LayerWord.enlargeWorkspace (W := W × J) _ hV
  have hc := (layerWord_tensor h (layerWord_one (I := J) d)).relabel
    (Equiv.sumProdDistrib I W J)
  convert hc using 1
  ext x y
  rcases x with ⟨i, j⟩ | ⟨w, j⟩ <;> rcases y with ⟨l, t⟩ | ⟨v, t⟩ <;>
    by_cases hj : j = t <;>
    simp [hj, Matrix.submatrix, Matrix.fromBlocks, Matrix.blockDiagonal_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P U : ι → Type}
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (U i)] [∀ i, DecidableEq (U i)]

/-- A single extra array of at most a constant multiple of the grid suffices
to process the axes in succession, at the cost of one word per axis. -/
theorem layerWord_grid_few {d c : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (hw : ∀ i, Fintype.card (U i) ≤ Fintype.card (P i) * (c - 1))
    (hV : Fintype.card (∀ i, P i) * (c - 1) ≤ Fintype.card V)
    (h : ∀ i, LayerWord d (fromBlocks (A i) 0 0 (1 : Matrix (U i) (U i) K))) :
    LayerWord (Fintype.card ι * d) (fromBlocks (gridTensor A) 0 0 (1 : Matrix V V K)) := by
  apply layerWord_grid_traverse_workspace
  intro i
  rw [axisMatrix_eq_blockDiagonal]
  apply OccupiedWord.relabel (e := (Equiv.piSplitAt i P).symm)
  apply (h i).parallelOccupiedCopies
  refine le_trans ?_ hV
  rw [Fintype.card_congr (Equiv.piSplitAt i P), Fintype.card_prod, Fintype.card_prod]
  calc
    _ ≤ (Fintype.card (P i) * (c - 1)) * _ := Nat.mul_le_mul_right _ (hw i)
    _ = _ := by ac_rfl

end FiniteFourier
end LinearAlgebra
end OAI
