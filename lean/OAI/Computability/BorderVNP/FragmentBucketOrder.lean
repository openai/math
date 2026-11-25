import OAI.Computability.BorderVNP.CrossingProfileScan

/-!
# Stable addresses for sparse fragment records

The count pass allocates one contiguous interval per cell. The scatter pass appends each
input record at the current cursor of its cell. The resulting order is exactly the
original input order restricted to that cell, including when some or all cells are empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open Crossing.Profile

variable {n cells : ℕ} (w : Fin n → Fin cells)

/-- Number of records assigned to a cell. -/
abbrev count := histogram w

/-- Number of records assigned to a cell among inputs strictly before position `t`. -/
abbrev prior := prefixCount w

/-- Exclusive prefix sum of the cell counts. -/
def start (k : ℕ) : ℕ :=
  ∑ c ∈ Finset.range k, if h : c < cells then count w ⟨c,h⟩ else 0

/-- The prefix scan starts at address zero. -/
theorem start_zero : start w 0 = 0 := by simp [start]

/-- Advancing to the next cell adds the complete width of the current cell. -/
theorem start_step (c : Fin cells) : start w (c.val+1) = start w c.val + count w c := by
  simp [start, Finset.sum_range_succ, c.isLt]

/-- Every input record contributes one to the sum of the cell counts. -/
theorem sum_count : ∑ c, count w c = n := by
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.cast_id] using (cableWidth w rfl (fun _ => 1)).symm

/-- The exclusive prefix just past the last cell is the number of records. -/
theorem start_end : start w cells = n := (Finset.sum_fin_eq_sum_range (count w)).symm.trans (sum_count w)

/-- All cell-local write cursors start at zero. -/
theorem prior_zero (c : Fin cells) : prior w 0 c = 0 := prefixCount_zero w c

/-- Reading one record increments precisely the cursor of its own cell. -/
theorem prior_step (i : Fin n) (c : Fin cells) :
    prior w (i.val+1) c = prior w i.val c + if w i = c then 1 else 0 :=
  prefixCount_step w i c

/-- When the scatter finishes, each cell has received its entire allocated count. -/
theorem prior_end (c : Fin cells) : prior w n c = count w c := prefixCount_end w c

private def inputSlot : (Σ c, Fin (count w c)) ≃ Fin n :=
  (Equiv.sigmaCongrRight fun c => (slots w c rfl).toEquiv.trans
    (Equiv.subtypeEquivRight fun i => by simp [positions] : positions w c ≃ {i // w i = c})).trans
    (Equiv.sigmaFiberEquiv w)

private def outputSlot : (Σ c, Fin (count w c)) ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr (sum_count w))

/-- The flattened address of a particular entry of the contiguous cell block. -/
def cellPos (c : Fin cells) (k : Fin (count w c)) : Fin n := outputSlot w ⟨c,k⟩

/-- Block address as computed by the exclusive prefix scan. -/
theorem cellPos_val (c : Fin cells) (k : Fin (count w c)) :
    (cellPos w c k).val = start w c.val + k.val := by
  change (finSigmaFinEquiv (n := count w) ⟨c,k⟩).val = _
  rw [finSigmaFinEquiv_apply, start, Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [dite_eq_left (a.isLt.trans c.isLt)]
  rfl

/-- Stable scatter, as a bijection from input row IDs onto the allocated output addresses. -/
def dest : Fin n ≃ Fin n := (inputSlot w).symm.trans (outputSlot w)

/-- The native destination is the cell base plus its cursor before the current record. -/
theorem dest_val (i : Fin n) : (dest w i).val = start w (w i).val + prior w i.val (w i) := by
  obtain ⟨⟨c,k⟩,rfl⟩ := (inputSlot w).surjective i
  have own : w (inputSlot w ⟨c,k⟩) = c := by
    exact (Finset.mem_filter.mp (slots w c rfl k).property).2
  have offset : prior w (inputSlot w ⟨c,k⟩).val c = k.val := prefixCount_slot w rfl c k
  rw [own, offset]
  simpa only [dest, cellPos, Equiv.trans_apply, Equiv.symm_apply_apply] using cellPos_val w c k

private theorem read_cell (c : Fin cells) (k : Fin (count w c)) :
    (dest w).symm (cellPos w c k) = (positions w c).orderEmbOfFin (rfl : _ = count w c) k := by
  change (inputSlot w) ((outputSlot w).symm ((outputSlot w) ⟨c,k⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem sorted_positions (c : Fin cells) :
    (positions w c).sort = (List.finRange n).filter fun i => w i = c := by
  let ids := (List.finRange n).filter fun i => w i = c
  have positions_eq : positions w c = ids.toFinset := by
    ext i
    simp [positions, ids]
  rw [positions_eq]
  apply (List.toFinset_sort (· ≤ ·) ((List.nodup_finRange _).filter _)).mpr
  apply List.Pairwise.filter
  rw [← Fin.sort_univ]
  exact Finset.pairwise_sort _ _

/-- Reading the scattered records across a cell gives exactly the original rows filtered
to this cell, in their original order. Payloads can be arbitrary, including repeated records. -/
theorem stable_cell {A : Type*} (value : Fin n → A) (c : Fin cells) :
    (List.finRange (count w c)).map (fun k => value ((dest w).symm (cellPos w c k))) =
      ((List.finRange n).filter fun i => w i = c).map value := by
  simp_rw [read_cell]
  have ids := (Finset.listMap_orderEmbOfFin_finRange (positions w c) (rfl : _ = count w c)).trans
    (sorted_positions w c)
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map value) ids

end FragmentBucket

end BorderVNP
end Computability
end OAI
