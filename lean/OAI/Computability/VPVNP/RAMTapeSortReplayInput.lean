import OAI.Computability.VPVNP.RAMTapeSortReplay
import OAI.Computability.VPVNP.RAMTapeRecordBuffer

/-! # Initial physical records of the sorting replay

A completed local transcript contributes its initialization and probe records
in their original order. The emitter then fills every remaining slot with
the canonical empty record. Its output bytes are exactly the input block for
the finite layer traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open BurstRAM RAMMemory RAMSort RAMSerialization RAMBoundary Boundary

variable {w : ℕ}

/-- Initial five-word records at all row indices of a site, including empty slots. -/
def emittedBlock (hw : 2 ≤ w) (e : ℕ) (records : List (WordRecord w)) : Wires (2+e) (RawSlot w) :=
  fun i => (recordFormat hw).words (RecordBuffer.slots (2^e) records (recordPosition e i))

theorem emittedBlock_canonical (hw : 2 ≤ w) (e : ℕ) (records : List (WordRecord w)) :
    CanonicalBlock hw (emittedBlock hw e records) := by
  intro i
  simp [Canonical, emittedBlock, Format.parse_words]

theorem recordBytes_words (hw : 2 ≤ w) (r : Option (WordRecord w)) :
    recordBytes ((recordFormat hw).words r) = List.ofFn ((recordFormat hw).encode r) := by
  have h := (SuccessorFields.raw_eq_flatten_words ((recordFormat hw).encode r)).symm
  simpa only [recordBytes, recordWords, Format.encode, Equiv.symm_apply_apply] using h

theorem emittedBlock_bytes (hw : 2 ≤ w) (e : ℕ) (records : List (WordRecord w)) :
    blockBytes (List.ofFn (emittedBlock hw e records)) =
      List.ofFn ((blockFormat (2^e) hw).encode (RecordBuffer.slots (2^e) records)) := by
  rw [RecordBuffer.block_serialized]
  simp only [blockBytes, RecordBuffer.serialized, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp [record_width])
  intro j hj hk
  simp only [List.getElem_ofFn, Function.comp_apply, emittedBlock, recordBytes_words]
  rfl

/-- The exact physical output of the record-emission routine supplies the
initial block of the finite sort without any data conversion. -/
theorem close_emittedBlock {hw : 2 ≤ w} {e : ℕ} {records : List (WordRecord w)}
    {s : Stacks RecordBuffer.Port} (h : RecordBuffer.Holds hw (2^e) records s) :
    RecordBuffer.close.Runs ((4*2^e-records.length)*(25*w+12)+1+(2*(4*2^e*5*w)+1)) s
      (Function.update (Function.update (Function.update s .remaining []) .reverseBuffer [])
        .output (blockBytes (List.ofFn (emittedBlock hw e records)))) := by
  rw [emittedBlock_bytes]
  exact h.close

/-- When the records came from this site's report stream, their checked
parse is the typed validator's local input array. -/
theorem decoded_emittedBlock (hw : 2 ≤ w) {e v start : ℕ} (header : ℕ → Word w)
    (rs : List (Report w)) (records : List (WordRecord w))
    (he : records.map WordRecord.record = initRecord header v :: probeRecords start rs) :
    decoded hw (emittedBlock hw e records) = localRecords header e v start rs := by
  funext i
  have hh := RecordBuffer.slots_eq_localRecords header rs records he i
  cases eqn : localRecords header e v start rs i with
  | mk r =>
    rw [eqn] at hh
    simp only [decoded, emittedBlock, parsedSlot, Format.parse_words]
    exact congrArg OrderedSlot.mk hh

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
