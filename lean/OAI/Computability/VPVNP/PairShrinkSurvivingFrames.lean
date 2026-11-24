import OAI.Computability.VPVNP.CompressorShrinkSliceSweep
import OAI.Computability.VPVNP.PairSimulationReverseSlices

/-!
# Copying one resident surviving interval back into its supply operand

The descriptor bank contains one source field and one target per subdivision.
The reverse copy reads the subdivision at offset zero and deposits it at the
sum of the preceding subdivision widths in the unsplit operand.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingFrames

open BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkPayload
open CompressorRecords CompressorRecords.SliceSchedule CompressorRecords.ShrinkSliceArrays
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Bit offset of a subdivision in its unsplit word. -/
def start (b q : ℕ) (j : Fin q) : ℕ := ((List.ofFn (splitWidth b q)).take j.val).sum

theorem bit_position (b q : ℕ) (pos : 0 < q) (j : Fin q) (i : Fin (splitWidth b q j)) :
    (sliceBits b q pos ⟨j, i⟩).val = start b q j + i.val := by
  rw [sliceBits_offset]
  simp [start, ← Fin.ofFn_take_eq_take_ofFn j.isLt.le, List.sum_ofFn, Fin.take]

theorem end_le (b q : ℕ) (pos : 0 < q) (j : Fin q) :
    start b q j + splitWidth b q j ≤ b := by
  let ws := List.ofFn (splitWidth b q)
  have hi : j.val < ws.length := by simp [ws]
  have full : ws.sum = b := List.sum_ofFn.trans (sum_splitWidth b q pos)
  have pieces := congrArg List.sum (List.take_append_drop (j.val + 1) ws)
  rw [List.sum_append, List.sum_take_succ _ _ hi, full] at pieces
  change (ws.take j.val).sum + splitWidth b q j ≤ b
  rw [show ws[j.val] = splitWidth b q j from List.getElem_ofFn ..] at pieces
  omega

/-- Physical location of the first of the frame's three public cells. -/
def head (row : ShrinkSliceSweep.Row w) (q : ℕ) (j : Fin q) :=
  frameHead row.bank.val 1 q + 3 * j.val

private theorem descriptor {b q : ℕ} {row : ShrinkSliceSweep.Row w} {mem : Memory w}
    (image : ShrinkSliceSweep.Image row b mem) (count : row.count.val = q) (j : Fin q) :
    (mem (head row q j + 2)).val = splitWidth b q j ∧
      (0 < splitWidth b q j → (mem (head row q j + 1)).val = 0 ∧
        (mem (head row q j)).val = start b q j) := by
  obtain ⟨before, staged, stored, same⟩ := image.descriptors
  rw [count] at stored same
  have pos := Nat.zero_lt_of_lt j.isLt
  let h := head row q j
  have bank (a : ℕ) (ha : a ≤ 2) : mem (h + a) = staged (h + a) := by
    apply same
    · dsimp [h, head, frameHead]; omega
    · simp only [stop, one_mul, h, head]
      have := j.isLt
      omega
  obtain ⟨len, offsets⟩ := surviving_frame b q pos stored j
  refine ⟨(congrArg Fin.val (bank 2 le_rfl)).trans len, ?_⟩
  intro hp
  let zero : Fin (splitWidth b q j) := ⟨0, hp⟩
  obtain ⟨ht, hs⟩ := offsets zero
  rw [bit_position] at hs
  refine ⟨(congrArg Fin.val (bank 1 (by decide))).trans ht, ?_⟩
  simpa only [Nat.add_zero, zero] using (congrArg Fin.val (bank 0 (by decide))).trans
    (Nat.add_right_cancel hs)

private theorem head_fit {row : ShrinkSliceSweep.Row w} {q : ℕ} (j : Fin q)
    (space : Workspace row.total row.dst row.bank 1 q) : head row q j + 2 < 2 ^ w := by
  apply lt_trans _ space.fits
  simp only [head, stop, one_mul]
  have := j.isLt
  omega

/-- The actual reverse header and private copy loop read this subdivision
from its native slot and write it at its designated unsplit offset. -/
theorem execute_piece {M : Machine w p r k} {pc : Fin 11 → Fin p}
    {reg : Fin 6 ↪ Fin r} {arcPC : Fin 7 → Fin p} {done : Fin p}
    (linked : ReverseSlices.Linked M pc reg (arcPC 0) done)
    (copy : PrivateFields.Linked M .copy arcPC (PrivateSlices.copyRegs reg) done)
    (c : Config w p r) (entry : c.pc = pc 0) (one : c.reg (reg 3) = 1)
    {row : ShrinkSliceSweep.Row w} {b q : ℕ} (j : Fin q) {mem : Memory w}
    (image : ShrinkSliceSweep.Image row b mem) (count : row.count.val = q)
    (space : Workspace row.total row.dst row.bank 1 q)
    (src dst : ℕ) (frame : c.reg (reg 5) = (head row q j : Word w))
    (source : c.reg (reg 0) = (src : Word w)) (destination : c.reg (reg 2) = (dst : Word w))
    (bits : Fin (splitWidth b q j) → Bool)
    (fit : 0 < splitWidth b q j → src + splitWidth b q j ≤ 2 ^ w ∧
      dst + start b q j + splitWidth b q j < 2 ^ w)
    (safe : 0 < splitWidth b q j → dst + start b q j ≤ src ∨
      src + splitWidth b q j ≤ dst + start b q j)
    (data : ∀ i, c.privateMem ((src + i.val : ℕ) : Word w) = PrivateFields.bitValue w (bits i)) :
    ReverseSlices.FrameResult M reg done c mem (head row q j : Word w)
      (dst + start b q j) (List.ofFn bits) := by
  let f : Word w := head row q j
  obtain ⟨len, offsets⟩ := descriptor image count j
  obtain ⟨lengthWord, offsetWords⟩ := ReverseSlices.oriented_frame_words true mem f
    (head row q j) (start b q j) 0 _ rfl (head_fit j space) len (fun h ↦ (offsets h).symm)
  apply ReverseSlices.execute_stored_frame true linked copy c entry one mem f frame
    src dst 0 (start b q j) source destination (List.ofFn bits)
  · simpa only [List.length_ofFn] using lengthWord
  · simpa only [List.length_ofFn, Bool.true_eq, ite_true] using offsetWords
  · simpa only [List.length_ofFn, Nat.add_zero] using fit
  · simpa only [List.length_ofFn, Nat.add_zero] using safe
  · intro i
    simpa only [Nat.add_zero, List.getElem_ofFn] using data ⟨i.val, by simpa using i.isLt⟩

end PairSimulation.ShrinkSurvivingFrames

end VPVNP
end Computability
end OAI
