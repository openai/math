import OAI.Computability.VPVNP.CompressorRecordsCopyIncidence
import OAI.Computability.VPVNP.CompressorSlotOutputLayout

/-!
# Address bounds for copying the shrinking incidence directory

The three base columns occupy shorter intervals than the three lane columns.
The destination reserves one full lane column per field. A single interval
comparison therefore suffices to schedule the six canonical copy scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CopyIncidence

open Compression SlotLevel ShrinkSlots BurstRAM

variable {a l w : ℕ} (Y : State a l) (s : SlotLevel.Shape) (h : Heads)

/-- The native copy worker scans exactly the initialized part of each output column. -/
theorem shrink_rows (baseRows : Fintype.card Y.Base*2^a = baseArcs s)
    (laneRows : Fintype.card Y.Base*2^l*2^a = actualCount s) (c : Fin 6) :
    rows Y c = if c.val < 3 then baseArcs s else actualCount s := by
  simp only [rows, State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv l),
    Fintype.card_fin, baseRows, laneRows]

/-- Every live source cell lies between the first base target and the last outgoing width. -/
theorem shrink_column_bounds (baseRows : Fintype.card Y.Base*2^a = baseArcs s)
    (laneRows : Fintype.card Y.Base*2^l*2^a = actualCount s) (scratchRoom : finish s h < 2^w) (c : Fin 6) :
    targetsHead s h ≤ ((directory s h w).column c).val ∧
      ((directory s h w).column c).val + rows Y c ≤ finish s h := by
  let head : Fin 6 → ℕ := ![targetsHead s h, inverseBaseHead s h, shiftsHead s h,
    outHead s h, inHead s h, widthHead s h]
  have b₁ : targetsHead s h + baseArcs s = shiftsHead s h := rfl
  have b₂ : shiftsHead s h + baseArcs s = inverseBaseHead s h := rfl
  have b₃ : inverseBaseHead s h + baseArcs s = outHead s h := rfl
  have b₄ : outHead s h + actualCount s = inHead s h := rfl
  have b₅ : inHead s h + actualCount s = widthHead s h := rfl
  have b₆ : widthHead s h + actualCount s = finish s h := rfl
  have source (c : Fin 6) : targetsHead s h ≤ head c ∧ head c + rows Y c ≤ finish s h := by
    rw [shrink_rows Y s baseRows laneRows]
    fin_cases c
    · change _ ≤ targetsHead s h ∧ targetsHead s h + baseArcs s ≤ _; omega
    · change _ ≤ inverseBaseHead s h ∧ inverseBaseHead s h + baseArcs s ≤ _; omega
    · change _ ≤ shiftsHead s h ∧ shiftsHead s h + baseArcs s ≤ _; omega
    · change _ ≤ outHead s h ∧ outHead s h + actualCount s ≤ _; omega
    · change _ ≤ inHead s h ∧ inHead s h + actualCount s ≤ _; omega
    · change _ ≤ widthHead s h ∧ widthHead s h + actualCount s ≤ _; omega
  have he : (directory s h w).column c = Fin.ofNat _ (head c) := by fin_cases c <;> rfl
  rw [he,Fin.val_ofNat,Nat.mod_eq_of_lt (by have := (source c).2; omega)]
  exact source c

/-- The descriptor's fixed column stride reserves all live rows of the selected state. -/
theorem packed_column_bounds (L : DescriptorSpace.Layout) (level : Fin L.levels)
    (laneRows : Fintype.card Y.Base*2^l*2^a = actualCount s) (levelRoom : DescriptorSpace.endAddress L < 2^w)
    (capacity : actualCount s ≤ DescriptorSpace.slotCapacity L) (c : Fin 6) :
    let start := DescriptorSpace.incidenceStart L level
    let n := actualCount s
    let U := DescriptorSpace.packedIncidence L w level n
    (U.column c).val = start+c.val*n ∧ (U.column c).val+rows Y c ≤ start+6*n := by
  intro start n U
  have room : start + 6*n < 2^w := DescriptorSpace.packed_incidence_room L levelRoom level capacity
  have destHead (c : Fin 6) : (U.column c).val = start+c.val*n := by
    rw [show U = DescriptorSpace.packedIncidence L w level n from rfl,DescriptorSpace.packed_column]
    have hc := Nat.mul_le_mul_right n c.isLt.le
    exact Nat.mod_eq_of_lt (by change start+c.val*n < _; omega)
  have counts (c : Fin 6) : rows Y c ≤ n := by
    have nr : Y.positions*2^a = n := by
      simpa only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv l),Fintype.card_fin] using laneRows
    exact (rows_le_slots Y c).trans_eq nr
  have dest (c : Fin 6) : (U.column c).val + rows Y c ≤ start + 6*n := by
    have hc := Nat.mul_le_mul_right n c.isLt
    rw [Nat.succ_mul] at hc
    rw [destHead]
    have := counts c; omega
  exact ⟨destHead c,dest c⟩

/-- The selected shrinking directory can be copied to the next descriptor
level whether the canonical output is below or above the scratch allocation. -/
theorem Regions.shrink_to_level (L : DescriptorSpace.Layout) (level : Fin L.levels)
    (baseRows : Fintype.card Y.Base*2^a = baseArcs s)
    (laneRows : Fintype.card Y.Base*2^l*2^a = actualCount s)
    (scratchRoom : finish s h < 2^w) (levelRoom : DescriptorSpace.endAddress L < 2^w)
    (capacity : actualCount s ≤ DescriptorSpace.slotCapacity L)
    (apart : finish s h ≤ DescriptorSpace.incidenceStart L level ∨
      DescriptorSpace.incidenceStart L level + 6 * actualCount s ≤ targetsHead s h) :
    Regions Y (directory s h w) (DescriptorSpace.packedIncidence L w level (actualCount s)) := by
  let T := directory s h w
  let U := DescriptorSpace.packedIncidence L w level (actualCount s)
  let start := DescriptorSpace.incidenceStart L level
  let n := actualCount s
  have source := shrink_column_bounds Y s h baseRows laneRows scratchRoom
  have packed := packed_column_bounds Y s L level laneRows levelRoom capacity
  have destHead (c : Fin 6) : (U.column c).val = start+c.val*n := (packed c).1
  have dest (c : Fin 6) : (U.column c).val + rows Y c ≤ start + 6*n := (packed c).2
  have counts (c : Fin 6) : rows Y c ≤ n := by
    rw [shrink_rows Y s baseRows laneRows]
    split
    · rw [← baseRows,show n = Fintype.card Y.Base*2^l*2^a from laneRows.symm]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))
    · exact le_rfl
  have room : start+6*n < 2^w := DescriptorSpace.packed_incidence_room L levelRoom level capacity
  apply Regions.of_intervals Y T U
  · intro c; exact (source c).2.trans scratchRoom.le
  · intro c; exact (dest c).trans room.le
  · intro c d
    change finish s h ≤ start ∨ start+6*n ≤ targetsHead s h at apart
    rcases apart with hf|hf
    · left; rw [destHead]; exact (source c).2.trans (hf.trans (Nat.le_add_right _ _))
    · right; exact (dest d).trans (hf.trans (source c).1)
  · intro c d hcd
    have before (i j : Fin 6) (lt : i < j) : (U.column i).val + rows Y i ≤ (U.column j).val := by
      have ij := Nat.mul_le_mul_right n (show i.val+1 ≤ j.val from lt)
      rw [Nat.succ_mul] at ij
      rw [destHead,destHead]
      have := counts i; omega
    exact (lt_or_gt_of_ne hcd).imp (before c d) (before d c)

end CompressorRecords.CopyIncidence

end VPVNP
end Computability
end OAI
