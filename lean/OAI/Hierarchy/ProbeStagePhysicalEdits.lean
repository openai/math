import OAI.Hierarchy.ProbeStageDirectoryWords
import OAI.Hierarchy.ProbeStageEndpoint

namespace OAI
/-! # The literal occurrence descriptors address the actual private mask words -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

abbrev ramWidth (h d : ℕ) := wordBits h d copies

def blockMaskBase (h d j : ℕ) (left : Bool) (b : Fin (groupBlocks h d j)) :=
  region h d j (maskArea left)+b.val*((radix h d)^4*fieldChunks h)

def packedPlace (h d j : ℕ) (left : Bool) (b : Fin (groupBlocks h d j)) (r : MaskIndex (radix h d)) (t : ℕ) : Word (ramWidth h d) :=
  (blockMaskBase h d j left b + (rowCode r*fieldChunks h+t) : ℕ)

theorem packedPlace_at {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (left : Bool) (b : Fin (groupBlocks h d j.val))
    (r : MaskIndex (radix h d)) (t : Fin (fieldChunks h)) :
    (packedPlace h d j.val left b r t.val).val=maskLocation h d j.val left b r t := by
  have room := region_word j.isLt (maskArea left) (mask_offset hd j.isLt.le b r t)
  unfold packedPlace
  rw [Fin.val_cast_of_lt (by simpa [blockMaskBase,Nat.add_assoc] using room)]
  simp [maskLocation,blockMaskBase,add_assoc]

theorem wordChunk {h : ℕ} (i : Fin (stringLength h)) : i.val/fieldWidth h < fieldChunks h := by
  apply (Nat.div_lt_iff_lt_mul (by simp [fieldWidth] : 0<fieldWidth h)).mpr
  exact i.isLt.trans_le (chunks_cover h).1

theorem packedPlace_eq {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (left : Bool) (b : Fin (groupBlocks h d j.val))
    (r x : MaskIndex (radix h d)) (t u : Fin (fieldChunks h)) :
    packedPlace h d j.val left b r t.val=packedPlace h d j.val left b x u.val ↔ r=x ∧ t=u := by
  rw [Fin.ext_iff,packedPlace_at hd,packedPlace_at hd]
  simp only [maskLocation,Nat.add_assoc,Nat.add_left_cancel_iff]
  constructor
  · intro eqn
    have hp : 0<fieldChunks h := by unfold fieldChunks;split <;> decide
    have dr := congrArg (· / fieldChunks h) eqn
    rw [Nat.mul_comm (rowCode r) (fieldChunks h),Nat.mul_comm (rowCode x) (fieldChunks h)] at dr
    simp only [Nat.mul_add_div hp,Nat.div_eq_of_lt t.isLt,Nat.div_eq_of_lt u.isLt,Nat.add_zero] at dr
    have re : r=x := finProdFinEquiv.injective (Fin.ext dr)
    subst x
    exact ⟨rfl,Fin.ext (Nat.add_left_cancel eqn)⟩
  · rintro ⟨rfl,rfl⟩;rfl

/-- Read the actual offset and mask word for ordinal `i` of the chosen color. Fixed ROM
addresses and mixed-radix offsets are word-sized by the bounds for this very phase. -/
theorem read_edit {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (left : Bool) (b : Fin (groupBlocks h d j.val))
    (mem : Memory (ramWidth h d)) (rom : immutable h d _ j mem) (v : MaskUpdate.Parameters (ramWidth h d))
    (c : Fin (radix h d)) (head : mem (v 1).val=((c.val*directoryCapacity (radix h d) (stringLength h):ℕ):Word _))
    (base : mem (v 2).val=(blockMaskBase h d j.val left b:Word _))
    (offsets : v 3=(region h d j.val 10:Word _)) (clearing : v 4=(region h d j.val 11:Word _))
    (i : ℕ) (hi : i<(PackedMask.occurrences (formatAdvice h d).row c).length) :
    ScatterRefinement.read v mem i = ScatterRefinement.event (fieldWidth h) (packedPlace h d j.val left b)
      (PackedMask.occurrences (formatAdvice h d).row c)[i] := by
  let off := c.val*directoryCapacity (radix h d) (stringLength h)+i
  have small := occurrence_offset hd c i hi
  have ptr : ScatterRefinement.index v mem i=(off:Word _) := by rw [ScatterRefinement.index,head,←Nat.cast_add]
  obtain ⟨ho,hc⟩ := occurrence_entries hd j mem rom c i hi
  dsimp only [off] at ptr
  simp only [ScatterRefinement.read,ptr,offsets,clearing,base]
  rw [add_word (region_word j.isLt 10 small),add_word (region_word j.isLt 11 small),ho,hc]
  simp only [ScatterRefinement.event,clearOffset,clearWord,packedPlace,Nat.cast_add]

end
end Hierarchy.ProbeStage.Native

end OAI
