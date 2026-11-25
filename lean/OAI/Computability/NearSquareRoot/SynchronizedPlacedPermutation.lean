import OAI.Computability.NearSquareRoot.SynchronizedPlacedTables
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Logic.Equiv.Fintype

/-! # Address tables for permutation slots in a borrowing batch

A physical row and column determine the local fiber and temporary rank on an
occupied cell. After permuting that rank, quotient and remainder convert the
new primary-cell address back to its physical coordinates. All padding and
unused cells keep their original address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedBorrowing
variable {a b c r : ℕ}

/-- Raw source coordinates read by one permutation slot. -/
def placedPermTarget (start v a r : ℕ) (f : ℕ → ℕ) (row col : ℕ) : ℕ × ℕ :=
  if col < a then
    match lookupRank start v a r (row*a+col) with
    | none => (row,col)
    | some (i,t) =>
      let x := physicalRank start v a r i (f t)
      (x/a,x%a)
  else (row,col)

/-- The physical row index and the padded column index. -/
def cellCoordinates (p : Fin b × (Fin a ⊕ Fin c)) : ℕ × ℕ :=
  (p.1.val,(finSumFinEquiv p.2).val)

theorem placedPermTarget_lookup (j : Fin 15) (f : ℕ → ℕ)
    (p : Fin b × (Fin a ⊕ Fin c)) :
    placedPermTarget (first b j) (size b j) a r f (cellCoordinates p).1 (cellCoordinates p).2 =
      match cellLookup r j p with
      | none => cellCoordinates p
      | some (i,t) =>
        let x := physicalRank (first b j) (size b j) a r i (f t)
        (x/a,x%a) := by
  unfold placedPermTarget cellLookup cellCoordinates
  by_cases h : (finSumFinEquiv p.2).val < a <;> simp [h]

theorem fullBatchCells_coordinates (hr : 2*r ≤ 8*a) (j : Fin 15)
    (q : (Fin a ⊕ Fin (2*r-a)) × Fin (size b j)) :
    let x := physicalRank (first b j) (size b j) a r q.2.val (finSumFinEquiv q.1).val
    cellCoordinates (fullBatchCells (c := c) hr j q) = (x/a,x%a) := by
  let t := batchPlacement b j hr (q.2,q.1)
  have h : t.2.val + a * t.1.val = _ :=
    placement_rank (batchFits b j) (show size b j ≤ b/8 from min_le_left _ _) hr q.2 q.1
  have ha := Nat.zero_lt_of_lt t.2.isLt
  change (t.1.val, t.2.val) = (_, _)
  rw [← h]
  simp [Nat.add_mul_div_left, ha, Nat.div_eq_of_lt t.2.isLt, Nat.mod_eq_of_lt t.2.isLt]

/-- Copies of the local permutation on occupied fibers, extended by the
identity on every other physical cell. -/
noncomputable def placedPermutation (hr : 2*r ≤ 8*a) (j : Fin 15)
    (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) : Equiv.Perm (Fin b × (Fin a ⊕ Fin c)) :=
  Equiv.Perm.viaFintypeEmbedding (e.prodCongr (Equiv.refl _)) (fullBatchCells hr j)

/-- The raw query enumerates the source coordinate of the placed permutation. -/
theorem placedPermutation_coordinates (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a)
    (j : Fin 15) (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) (f : ℕ → ℕ)
    (hf : ∀ t, f (finSumFinEquiv t).val = (finSumFinEquiv (e t)).val)
    (p : Fin b × (Fin a ⊕ Fin c)) :
    cellCoordinates (placedPermutation hr j e p) =
      placedPermTarget (first b j) (size b j) a r f (cellCoordinates p).1 (cellCoordinates p).2 := by
  rw [placedPermTarget_lookup]
  by_cases hp : p ∈ Set.range (fullBatchCells hr j)
  · obtain ⟨q,rfl⟩ := hp
    rw [cellLookup_placed ha har, placedPermutation, Equiv.Perm.viaFintypeEmbedding_apply_image]
    rcases q with ⟨t,i⟩
    simpa only [hf, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply] using
      fullBatchCells_coordinates (c := c) hr j (e t,i)
  · rw [(cellLookup_eq_none_iff ha har hr j p).mpr hp, placedPermutation,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hp]

/-- The target is an actual address in the padded physical rectangle. -/
theorem placedPermTarget_lt (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a)
    (j : Fin 15) (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) (f : ℕ → ℕ)
    (hf : ∀ t, f (finSumFinEquiv t).val = (finSumFinEquiv (e t)).val)
    (p : Fin b × (Fin a ⊕ Fin c)) :
    let t := placedPermTarget (first b j) (size b j) a r f (cellCoordinates p).1 (cellCoordinates p).2
    t.1 < b ∧ t.2 < a+c := by
  rw [← placedPermutation_coordinates ha har hr j e f hf p]
  exact ⟨(placedPermutation hr j e p).1.isLt, (finSumFinEquiv (placedPermutation hr j e p).2).isLt⟩

/-- A row of the batch matrix reads the permuted physical cell. -/
theorem placedPermutation_mulVec (hr : 2*r ≤ 8*a) (j : Fin 15)
    (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) (x : Fin b × (Fin a ⊕ Fin c) → ℂ)
    (p : Fin b × (Fin a ⊕ Fin c)) :
    (batchMatrix hr j e.toPEquiv.toMatrix *ᵥ x) p = x (placedPermutation hr j e p) := by
  change (placeHom (fullBatchCells hr j) _ *ᵥ x) p = _
  rw [placeHom_mulVec]
  by_cases hp : p ∈ Set.range (fullBatchCells hr j)
  · obtain ⟨q,rfl⟩ := hp
    rw [(fullBatchCells hr j).injective.extend_apply, placedPermutation,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
    rcases q with ⟨t,i⟩
    simp [mulVec, dotProduct, PEquiv.toMatrix_apply]
  · rw [Function.extend_apply' _ _ _ hp, placedPermutation,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hp]

/-- Reading numerical records through the raw table realizes the same matrix action. -/
theorem placedPermTarget_mulVec (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a)
    (j : Fin 15) (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) (f : ℕ → ℕ)
    (hf : ∀ t, f (finSumFinEquiv t).val = (finSumFinEquiv (e t)).val)
    (x : ℕ × ℕ → ℂ) (p : Fin b × (Fin a ⊕ Fin c)) :
    (batchMatrix hr j e.toPEquiv.toMatrix *ᵥ (x ∘ cellCoordinates)) p =
      x (placedPermTarget (first b j) (size b j) a r f (cellCoordinates p).1 (cellCoordinates p).2) := by
  rw [placedPermutation_mulVec, Function.comp_apply, placedPermutation_coordinates ha har hr j e f hf]

theorem placedPermutation_matrix (hr : 2*r ≤ 8*a) (j : Fin 15)
    (e : Equiv.Perm (Fin a ⊕ Fin (2*r-a))) :
    batchMatrix (b := b) (c := c) hr j e.toPEquiv.toMatrix =
      (placedPermutation hr j e).toPEquiv.toMatrix := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  funext p
  rw [placedPermutation_mulVec]
  simp [mulVec, dotProduct, PEquiv.toMatrix_apply]

/-- Transport the two-half permutation into the active/borrowed indexing. -/
noncomputable def borrowedPermutation (har : a ≤ r) (e : Equiv.Perm (Fin r ⊕ Fin r)) :
    Equiv.Perm (Fin a ⊕ Fin (2*r-a)) :=
  (auxiliaryLayout har).permCongr e

theorem borrowedPermutation_rank (har : a ≤ r) (e : Equiv.Perm (Fin r ⊕ Fin r)) (f : ℕ → ℕ)
    (hf : ∀ t, f (finSumFinEquiv t).val = (finSumFinEquiv (e t)).val)
    (t : Fin a ⊕ Fin (2*r-a)) :
    f (finSumFinEquiv t).val = (finSumFinEquiv (borrowedPermutation har e t)).val := by
  obtain ⟨t,rfl⟩ := (auxiliaryLayout har).surjective t
  simpa [borrowedPermutation, Equiv.permCongr_apply, auxiliaryLayout] using hf t

theorem borrowedPermutation_matrix (har : a ≤ r) (e : Equiv.Perm (Fin r ⊕ Fin r)) :
    (e.toPEquiv.toMatrix (α := ℂ)).submatrix (auxiliaryLayout har).symm (auxiliaryLayout har).symm =
      (borrowedPermutation har e).toPEquiv.toMatrix := by
  ext x y
  simp only [submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
    borrowedPermutation, Equiv.permCongr_apply, Equiv.eq_symm_apply]

theorem placedHalfPermutation_matrix (har : a ≤ r) (hr : 2*r ≤ 8*a) (j : Fin 15)
    (e : Equiv.Perm (Fin r ⊕ Fin r)) :
    batchMatrix (b := b) (c := c) hr j
      (e.toPEquiv.toMatrix.submatrix (auxiliaryLayout har).symm (auxiliaryLayout har).symm) =
      (placedPermutation hr j (borrowedPermutation har e)).toPEquiv.toMatrix := by
  rw [borrowedPermutation_matrix, placedPermutation_matrix]

end ShortFourier

end NearSquareRoot
end Computability
end OAI
