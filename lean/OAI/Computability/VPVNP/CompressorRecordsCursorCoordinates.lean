import OAI.Computability.VPVNP.CursorState
import OAI.Computability.VPVNP.BitSlotXor

/-!
# Numerical coordinates for the initial compressor graph

The RAM visits outgoing slots in cursor, base-address, lane and slot order.
Physical address bits have increasing significance, whereas the compressor
numbers each binary block with its first coordinate most significant. Reversing
the coordinates within each designated block identifies the cursor's one-bit
flip with the corresponding power of two in its RAM word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Compression (BitWord bitWordFinEquiv bitWordFinEquiv_val bitWordFinEquiv_add_val)

variable {b l a p : ℕ} {S : Type} [Fintype S]

/-- Designate a low base-address block and a high lane block. Each compressor
block is ordered most significant bit first. -/
def cursorCoordinateLabels (b l : ℕ) : Fin (b + l) ≃ Fin b ⊕ Fin l :=
  finSumFinEquiv.symm.trans (Fin.revPerm.sumCongr Fin.revPerm)

/-- Cursor-major base numbering. -/
def cursorBaseIndex (b l : ℕ) : Fin (b + l) × BitWord b ≃ Fin ((b + l) * 2 ^ b) :=
  ((Equiv.refl _).prodCongr (bitWordFinEquiv b)).trans finProdFinEquiv

/-- Base-major numbering of positions, with consecutive lanes. -/
def cursorActualIndex (b l : ℕ) :
    (Fin (b + l) × BitWord b) × BitWord l ≃ Fin (((b + l) * 2 ^ b) * 2 ^ l) :=
  ((cursorBaseIndex b l).prodCongr (bitWordFinEquiv l)).trans finProdFinEquiv

/-- Source or destination slot in the base records. -/
def cursorBaseSlotNumber (e : (Fin (b + l) × BitWord b) × Fin (2 ^ a)) : ℕ :=
  (cursorBaseIndex b l e.1).val * 2 ^ a + e.2.val

/-- Source or destination slot in the actual-wire records. -/
def cursorActualSlotNumber (e : ((Fin (b + l) × BitWord b) × BitWord l) × Fin (2 ^ a)) : ℕ :=
  (cursorActualIndex b l e.1).val * 2 ^ a + e.2.val

theorem cursorBaseIndex_val (j : Fin (b + l)) (x : BitWord b) :
    (cursorBaseIndex b l (j,x)).val = j.val * 2 ^ b + (bitWordFinEquiv b x).val := by
  change (bitWordFinEquiv b x).val + 2 ^ b * j.val = _
  ac_rfl

theorem cursorActualIndex_val (v : Fin (b + l) × BitWord b) (g : BitWord l) :
    (cursorActualIndex b l (v,g)).val =
      (cursorBaseIndex b l v).val * 2 ^ l + (bitWordFinEquiv l g).val := by
  change (bitWordFinEquiv l g).val + 2 ^ l * (cursorBaseIndex b l v).val = _
  ac_rfl

/-- The record numbering agrees with the indexed vertex order used by
the greedy scans on the initial compressor state. -/
theorem cursorState_baseIndex_val (hD : 1 < b + l) (hd : 2 + p = 2 ^ a) (bits : S → ℕ)
    (v : Fin (b + l) × BitWord b) :
    ((cursorState (cursorCoordinateLabels b l) hD hd bits).baseIndex v).val =
      (cursorBaseIndex b l v).val := rfl

/-- Numeric destination vertex of a base slot. -/
def cursorNextBase (b l j x i : ℕ) : ℕ :=
  ((j + 1) % (b + l)) * 2 ^ b + (x ^^^ (if i = 1 ∧ j < b then 2 ^ j else 0))

/-- Numeric lane displacement of the slot. -/
def cursorLaneMask (b j i : ℕ) : ℕ :=
  if i = 1 ∧ b ≤ j then 2 ^ (j - b) else 0

private theorem bitWord_zero (n : ℕ) : (bitWordFinEquiv n 0).val = 0 := by
  simpa using bitWordFinEquiv_add_val (0 : BitWord n) 0

private theorem bitWord_single {n : ℕ} (j : Fin n) :
    (bitWordFinEquiv n (fun k ↦ if k = j.rev then 1 else 0)).val = 2 ^ j.val := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    induction j using Fin.lastCases with
    | last =>
      have ht : Fin.tail (fun k : Fin (n + 1) ↦ if k = (Fin.last n).rev then
          (1 : ZMod 2) else 0) = 0 := by
        funext k
        simp [Fin.tail]
      rw [bitWordFinEquiv_val, ht, bitWord_zero]
      simp
      decide
    | cast j =>
      have ht : Fin.tail (fun k : Fin (n + 1) ↦ if k = j.castSucc.rev then
          (1 : ZMod 2) else 0) = (fun k ↦ if k = j.rev then 1 else 0) := by
        funext k
        simp [Fin.tail, Fin.rev_castSucc]
      rw [bitWordFinEquiv_val, ht, ih]
      simp [Fin.rev_castSucc, (Fin.succ_ne_zero _).symm]

private theorem padding_slot_flip (i : Fin (2 + p)) : slotSide i = true ↔ i.val = 1 := by
  obtain ⟨s | k, rfl⟩ := (paddingSlots p).surjective i
  · rw [slotSide_real]
    cases s with
    | false => exact (by decide : (false = true ↔ (0 : ℕ) = 1))
    | true => exact (by decide : (true = true ↔ (1 : ℕ) = 1))
  · rw [slotSide_pad]
    change false = true ↔ 2 + k.val = 1
    simp; omega

private theorem partition_base (j : Fin (b + l)) (side : Bool) :
    (bitWordFinEquiv b ((addressPartition (cursorCoordinateLabels b l)
      (stepShift j side)).1)).val = if side = true ∧ j.val < b then 2 ^ j.val else 0 := by
  by_cases h : side = true ∧ j.val < b
  · let t : Fin b := ⟨j.val, h.2⟩
    have he : (addressPartition (cursorCoordinateLabels b l) (stepShift j side)).1 =
        (fun k ↦ if k = t.rev then 1 else 0) := by
      funext k
      change (if side = true ∧ j = k.rev.castAdd l then (1 : ZMod 2) else 0) = _
      have hj : j = k.rev.castAdd l ↔ k = t.rev := by
        rw [← Fin.rev_inj (i := k) (j := t.rev), Fin.rev_rev, eq_comm (a := k.rev)]
        rw [Fin.ext_iff, Fin.ext_iff]
        rfl
      simp [hj, h.1]
    rw [he, bitWord_single, ite_eq_left h]
  · have he : (addressPartition (cursorCoordinateLabels b l) (stepShift j side)).1 = 0 := by
      funext k
      change (if side = true ∧ j = k.rev.castAdd l then (1 : ZMod 2) else 0) = 0
      exact ite_eq_right (fun ⟨hs, he⟩ ↦ h ⟨hs, he ▸ k.rev.isLt⟩)
    rw [he, bitWord_zero, ite_eq_right h]

private theorem partition_lane (j : Fin (b + l)) (side : Bool) :
    (bitWordFinEquiv l ((addressPartition (cursorCoordinateLabels b l)
      (stepShift j side)).2)).val = if side = true ∧ b ≤ j.val then 2 ^ (j.val - b) else 0 := by
  by_cases h : side = true ∧ b ≤ j.val
  · let t : Fin l := ⟨j.val - b, by have := j.isLt; omega⟩
    have he : (addressPartition (cursorCoordinateLabels b l) (stepShift j side)).2 =
        (fun k ↦ if k = t.rev then 1 else 0) := by
      funext k
      change (if side = true ∧ j = k.rev.natAdd b then (1 : ZMod 2) else 0) = _
      have hj : j = k.rev.natAdd b ↔ k = t.rev := by
        rw [← Fin.rev_inj (i := k) (j := t.rev), Fin.rev_rev, Fin.ext_iff, Fin.ext_iff]
        change j.val = b + k.rev.val ↔ k.rev.val = j.val - b
        omega
      simp [hj, h.1]
    rw [he, bitWord_single, ite_eq_left h]
  · have he : (addressPartition (cursorCoordinateLabels b l) (stepShift j side)).2 = 0 := by
      funext k
      change (if side = true ∧ j = k.rev.natAdd b then (1 : ZMod 2) else 0) = 0
      exact ite_eq_right (fun ⟨hs, he⟩ ↦ h ⟨hs, he ▸ Nat.le_add_right b _⟩)
    rw [he, bitWord_zero, ite_eq_right h]

variable (hD : 1 < b + l) (hd : 2 + p = 2 ^ a) (bits : S → ℕ)

private theorem cursorNextIndex (j : Fin (b + l)) (x : BitWord b) (i : Fin (2 ^ a)) :
    (cursorBaseIndex b l
      ((cursorState (cursorCoordinateLabels b l) hD hd bits).slots.base.target ((j,x),i)).1).val =
      cursorNextBase b l j.val (bitWordFinEquiv b x).val i.val := by
  let side := slotSide ((finCongr hd).symm i)
  change (cursorBaseIndex b l (finRotate (b + l) j,
    x + (addressPartition (cursorCoordinateLabels b l) (stepShift j side)).1)).val = _
  have hs : side = true ↔ i.val = 1 := padding_slot_flip _
  have : NeZero (b + l) := ⟨by omega⟩
  rw [cursorBaseIndex_val, bitWordFinEquiv_add_val, partition_base, finRotate_apply,
    Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hD]
  simp only [hs, cursorNextBase]

/-- Each outgoing base slot writes its own incoming slot number at the
rotated cursor and the updated base address. -/
theorem cursorBaseTargetNumber (j : Fin (b + l)) (x : BitWord b) (i : Fin (2 ^ a)) :
    cursorBaseSlotNumber
      ((cursorState (cursorCoordinateLabels b l) hD hd bits).slots.base.target ((j,x),i)) =
      cursorNextBase b l j.val (bitWordFinEquiv b x).val i.val * 2 ^ a + i.val := by
  exact congrArg (fun n : ℕ ↦ n * 2 ^ a + i.val) (cursorNextIndex hD hd bits j x i)

/-- The stored displacement is the translated physical bit of the lane block. -/
theorem cursorDisplacementNumber (j : Fin (b + l)) (x : BitWord b) (i : Fin (2 ^ a)) :
    (bitWordFinEquiv l
      ((cursorState (cursorCoordinateLabels b l) hD hd bits).slots.displacement ((j,x),i))).val =
      cursorLaneMask b j.val i.val := by
  let side := slotSide ((finCongr hd).symm i)
  change (bitWordFinEquiv l
    ((addressPartition (cursorCoordinateLabels b l) (stepShift j side)).2)).val = _
  have hs : side = true ↔ i.val = 1 := padding_slot_flip _
  simp only [partition_lane, hs, cursorLaneMask]

/-- Flattening the actual graph's target into a record address updates
the base and lane separately and preserves the slot. -/
theorem cursorActualTargetNumber (j : Fin (b + l)) (x : BitWord b) (g : BitWord l)
    (i : Fin (2 ^ a)) :
    cursorActualSlotNumber
      ((cursorState (cursorCoordinateLabels b l) hD hd bits).slots.actualGraph.target (((j,x),g),i)) =
      (cursorNextBase b l j.val (bitWordFinEquiv b x).val i.val * 2 ^ l +
        ((bitWordFinEquiv l g).val ^^^ cursorLaneMask b j.val i.val)) * 2 ^ a + i.val := by
  let G : Compression.LiftedSlots (Fin (b + l) × BitWord b) (2 ^ a) (BitWord l) :=
    (cursorState (cursorCoordinateLabels b l) hD hd bits).slots
  change (cursorActualIndex b l ((G.base.target ((j,x),i)).1,
    g + G.displacement ((j,x),i))).val * 2 ^ a + i.val = _
  rw [cursorActualIndex_val, bitWordFinEquiv_add_val]
  have hb := cursorNextIndex hD hd bits j x i
  have hl := cursorDisplacementNumber hD hd bits j x i
  change (cursorBaseIndex b l (G.base.target ((j,x),i)).1).val = _ at hb
  change (bitWordFinEquiv l (G.displacement ((j,x),i))).val = _ at hl
  rw [hb, hl]

private theorem numbered_width {D : ℕ} (v : Position D) (i : Fin (2 + p)) :
    paddedWidth bits ((paddedEdgeEquiv D p).symm (v,i)) = if i.val < 2 then ∑ s, bits s else 0 := by
  obtain ⟨s | k, rfl⟩ := (paddingSlots p).surjective i
  · change paddedWidth bits (match (paddingSlots p).symm (paddingSlots p (.inl s)) with
      | .inl t => .inl (v.1,v.2,t) | .inr u => .inr (v,u)) = _
    rw [Equiv.symm_apply_apply]
    exact (ite_eq_left ((finTwoEquiv.symm s).isLt)).symm
  · change paddedWidth bits (match (paddingSlots p).symm (paddingSlots p (.inr k)) with
      | .inl t => .inl (v.1,v.2,t) | .inr u => .inr (v,u)) = _
    rw [Equiv.symm_apply_apply]
    exact (ite_eq_right (show ¬2 + k.val < 2 by omega)).symm

/-- Stay and flip wires reserve all fields. Each further slot is a zero-width copy. -/
theorem cursorSlotWidth (j : Fin (b + l)) (x : BitWord b) (g : BitWord l) (i : Fin (2 ^ a)) :
    (cursorState (cursorCoordinateLabels b l) hD hd bits).width (((j,x),i),g) =
      if i.val < 2 then ∑ s, bits s else 0 :=
  numbered_width bits ((lanePositions (cursorCoordinateLabels b l)).symm ((j,x),g))
    ((finCongr hd).symm i)

end CursorNetwork

end VPVNP
end Computability
end OAI
