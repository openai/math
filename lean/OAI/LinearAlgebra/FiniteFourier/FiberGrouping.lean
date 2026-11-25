import OAI.LinearAlgebra.FiniteFourier.OccupiedAxes

/-! # Grouping the axes of a large tensor product

Partition the axes into groups of comparable size. A tensor product of the
group words has the same depth as any one group, after padding.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped BigOperators

variable {K : Type*} [CommSemiring K] {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Type}
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Tensor words for the groups of any partition of the axes. -/
theorem layerWord_grid_regroup {B : Type} [Fintype B] [DecidableEq B]
    {F : B → Type} [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
    (e : (Σ j, F j) ≃ ι) {d : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (h : ∀ j, LayerWord d (gridTensor fun u : F j => A (e ⟨j, u⟩))) :
    LayerWord d (gridTensor A) := by
  let rearrange := (Equiv.piCongrLeft P e).symm.trans
    (Equiv.piCurry fun j (u : F j) => P (e ⟨j, u⟩))
  have hword := (layerWord_grid h).relabel rearrange.symm
  convert hword using 1
  ext x y
  change (∏ i, A i (x i) (y i)) =
    ∏ j, ∏ u : F j, A (e ⟨j, u⟩) (x (e ⟨j, u⟩)) (y (e ⟨j, u⟩))
  rw [← e.prod_comp fun i => A i (x i) (y i)]
  exact Fintype.prod_sigma _

/-- When there are at least `k` axes, partitioning the axes keeps the tensor
depth independent of their total number and restores all borrowed registers. -/
theorem layerWord_grid_many {W : ι → Type} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    {d c k : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (hk : 0 < k) (hki : k ≤ Fintype.card ι) (hc : 0 < c) (hck : c ≤ 2 ^ (k - 1))
    (ha : ∀ i, 2 ≤ Fintype.card (P i))
    (hw : ∀ i, Fintype.card (W i) ≤ Fintype.card (P i) * (c - 1))
    (h : ∀ i, LayerWord d (Matrix.fromBlocks (A i) 0 0 (1 : Matrix (W i) (W i) K))) :
    LayerWord ((2 * k - 1) * ((2 * c - 1) * d)) (gridTensor A) := by
  obtain ⟨b, size, hs, ⟨e⟩⟩ := exists_fiber_partition ι hk hki
  apply layerWord_grid_regroup e.symm
  intro j
  let idx (u : Fin (size j)) := e.symm ⟨j, u⟩
  apply layerWord_grid_block (W := fun u => W (idx u)) hc hck
  · simpa using (hs j).1
  · rw [Fintype.card_fin]
    have := (hs j).2
    omega
  · exact fun u => ha (idx u)
  · exact fun u => hw (idx u)
  · exact fun u => h (idx u)

end FiniteFourier
end LinearAlgebra
end OAI
