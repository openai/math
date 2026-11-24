import OAI.Computability.VPVNP.RAMTapeRecords
import OAI.Computability.VPVNP.RAMTapeRecordClose
import OAI.Computability.VPVNP.RAMBitTranscript

/-!
# Relating the emitted tape records to the site's initial sorting array

One invocation of the record callback extends the accumulated prefix by the
canonical bits of the staged record. Closing an admitted prefix adds just the
vacant physical slots. Its decoded wire array is the `localRecords` input to
the distributed validator, including the initialization record at sites with
no calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RecordBuffer

open BurstRAM RAMMemory RAMSerialization

variable {w H : ℕ}

/-- Between emissions all output bits are on the reverse buffer, and every
free slot is represented by one true mark. -/
structure Holds (hw : 2 ≤ w) (H : ℕ) (records : List (WordRecord w)) (s : Stacks Port) : Prop where
  fit : records.length ≤ 4*H
  scratch : s .temp = []
  zeros : s .zeros = List.replicate w false
  remaining : s .remaining = List.replicate (4*H-records.length) true
  buffer : s .reverseBuffer = (serialized hw (records.map some)).reverse
  output : s .output = []

/-- Constructing a single probe or initialization record does not change
the caller's five word registers. It extends the physical array once. -/
theorem Holds.emit {hw : 2 ≤ w} {records : List (WordRecord w)} {s : Stacks Port}
    (h : Holds hw H records s) (hfree : records.length < 4*H) (r : WordRecord w)
    (hf : ∀ j, s (.field j) = BurstRAM.wordBits ((recordFormat hw).words (some r) j)) :
    let left := List.replicate (4*H-(records.length+1)) true
    let t := emitted s left (List.ofFn ((recordFormat hw).encode (some r)))
    appendRecord.Runs (25*w+12) s t ∧ Holds hw H (records++[r]) t := by
  dsimp only
  have hlen : 4*H-records.length = 4*H-(records.length+1)+1 := by omega
  refine ⟨appendRecord_run hw (some r) s _ (by rw [h.remaining, hlen, List.replicate_succ]) h.scratch hf,
    ⟨by simp; omega, by simpa [emitted] using h.scratch, by simpa [emitted] using h.zeros, ?_, ?_,
      by simpa [emitted] using h.output⟩⟩
  · simp [emitted]
  · simp [emitted, h.buffer, serialized, List.reverse_append]

/-- The remaining indices return the unique empty slot. -/
def slots (H : ℕ) (records : List (WordRecord w)) : Fin (4*H) → Option (WordRecord w) :=
  fun i => records[i.val]?

theorem slots_list (H : ℕ) (records : List (WordRecord w)) (hfit : records.length ≤ 4*H) :
    List.ofFn (slots H records) = records.map some ++ List.replicate (4*H-records.length) none := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4*H
  · rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hj), List.getElem_ofFn]
    change some (records[j]?) = _
    by_cases h : j < records.length
    · rw [List.getElem?_append_left (by simpa using h), List.getElem?_map, List.getElem?_eq_getElem h]
      rfl
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h), List.length_map,
        List.getElem?_eq_none (Nat.le_of_not_gt h)]
      simp [show j-records.length < 4*H-records.length by omega]
  · have hl : (records.map some ++ List.replicate (4*H-records.length) (none : Option (WordRecord w))).length
        = 4*H := by simp only [List.length_append, List.length_map, List.length_replicate]; omega
    rw [List.getElem?_eq_none (by simp only [List.length_ofFn]; omega),
      List.getElem?_eq_none (by rw [hl]; omega)]

theorem Holds.close {hw : 2 ≤ w} {records : List (WordRecord w)} {s : Stacks Port}
    (h : Holds hw H records s) :
    RecordBuffer.close.Runs ((4*H-records.length)*(25*w+12)+1+(2*(4*H*5*w)+1)) s
      (Function.update (Function.update (Function.update s .remaining []) .reverseBuffer []) .output
        (List.ofFn ((blockFormat H hw).encode (slots H records)))) :=
  close_block hw _ s _ _ (slots_list H records h.fit) h.scratch h.zeros h.remaining h.buffer h.output

/-- Widening the emitted slots, in order, recovers the complete typed input
to the actual Batcher sorting replay. -/
theorem slots_eq_localRecords {e v start : ℕ} (header : ℕ → Word w) (rs : List (Report w))
    (records : List (WordRecord w))
    (hrecs : records.map WordRecord.record = initRecord header v :: probeRecords start rs)
    (i : Fin (2^(2+e))) :
    ((slots (2^e) records (recordPosition e i)).map WordRecord.record) =
      (localRecords header e v start rs i).record := by
  let a := records.map WordRecord.record
  have hj : (recordPosition e i).val = i.val := rfl
  simp only [slots, hj, ← List.getElem?_map, hrecs, localRecords, siteRecordBlock]
  let occupied := initRecord header v :: probeRecords start rs
  change occupied[i.val]? = ((occupied.map some ++ List.replicate _ none)[i.val]?).getD none
  by_cases h : i.val < occupied.length
  · rw [List.getElem?_append_left (by simpa using h), List.getElem?_map, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h), List.length_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]
    simp

end RAMTape.RecordBuffer

end VPVNP
end Computability
end OAI
