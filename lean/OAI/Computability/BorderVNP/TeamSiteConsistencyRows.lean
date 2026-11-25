import OAI.Computability.BorderVNP.TeamEventRecords
import OAI.Computability.BorderVNP.TeamTapeInputEmitChunks
import OAI.Computability.BorderVNP.TeamTapeSortingLayout

/-! # Chronology of the interleaved physical team rows

Each real sorter block starts with the local literal and exterior input, followed by
that processor's successive ordinary and burst probes. The complete rows are a
permutation of the logical chronology, with every physical phase and payload fixed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape RAMSerialization TeamRAM TeamEventRecords
open BurstRAM (Word Memory)
open TeamProbeEmit (widen widenRecord)
variable {w r : ℕ}

/-- Charged time offset of a real site's first instruction, before adding the initial tick. -/
def blockOffset (blocks : Fin r → List (Event w)) (j : Fin r) : ℕ :=
  RAMBuckets.cost (fun e => e.action.extra) ((List.ofFn blocks).take j.val).flatten

/-- Typed slots appended by the real instruction interpreter. -/
abbrev historySlots {w : ℕ} := @TeamEventRecords.historySlots w

/-- Local chronological four-word fields in the real buffer's interleaved order. -/
def rowFields (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) (j : Fin r) :
    List (TeamRecords.Record (Word (w+1))) :=
  TeamTapeInputEmit.probes (w+1) (TeamTapeInputEmit.rowStart input j) (input j) ++
    (historyFields (1+blockOffset blocks j) (blocks j)).map widenRecord

/-- Typed slots entering the real processor's final memory pass. -/
def realRows (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) (j : Fin r) :
    List (WordRecord (w+1)) :=
  TeamTapeInputEmit.records (w+1) (TeamTapeInputEmit.rowStart input j) (input j) ++
    historySlots (1+blockOffset blocks j) (blocks j)

/-- Logical chronology, with all initializations preceding the whole block trace. -/
def chronology (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) :
    List (TeamRecords.Record (Word (w+1))) :=
  TeamTapeInputEmit.probes (w+1) 0 (List.ofFn input).flatten ++
    (historyFields 1 (List.ofFn blocks).flatten).map widenRecord

private theorem probes_append (k a : ℕ) (xs ys : List Bool) :
    TeamTapeInputEmit.probes k a (xs++ys) = TeamTapeInputEmit.probes k a xs ++
      TeamTapeInputEmit.probes k (a+xs.length) ys := by
  induction xs generalizing a with
  | nil => simp [TeamTapeInputEmit.probes]
  | cons x xs ih =>
    simp only [List.cons_append,TeamTapeInputEmit.probes,ih,List.length_cons]
    rw [show a+1+xs.length = a+(xs.length+1) by omega]

private theorem flatten_input (k a : ℕ) (input : Fin r → List Bool) :
    (List.ofFn fun j => TeamTapeInputEmit.probes k (a+TeamTapeInputEmit.rowStart input j) (input j)).flatten =
      TeamTapeInputEmit.probes k a (List.ofFn input).flatten := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons, probes_append]
    simp only [TeamTapeInputEmit.rowStart, Fin.val_zero, List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero]
    congr 1
    rw [← ih (a+(input 0).length) (fun i => input i.succ)]
    simp [TeamTapeInputEmit.rowStart,List.ofFn_succ,Nat.add_assoc]

private theorem flatten_blocks (t : ℕ) (blocks : Fin r → List (Event w)) :
    (List.ofFn fun j => historyFields (t+blockOffset blocks j) (blocks j)).flatten =
      historyFields t (List.ofFn blocks).flatten := by
  induction r generalizing t with
  | zero => rfl
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons, history_append]
    simp only [blockOffset,Fin.val_zero,List.take_zero,List.flatten_nil,RAMBuckets.cost,Nat.add_zero]
    congr 1
    rw [← ih (t+RAMBuckets.cost (fun e => e.action.extra) (blocks 0)) (fun i => blocks i.succ)]
    simp [blockOffset,List.ofFn_succ,Nat.add_assoc]

private theorem interleave {α : Type*} (xs ys : Fin r → List α) :
    ((List.ofFn xs).flatten++(List.ofFn ys).flatten).Perm
      (List.ofFn fun j => xs j++ys j).flatten := by
  have h := List.flatMap_append_perm (List.ofFn (id : Fin r → Fin r)) xs ys
  simpa only [List.flatMap_def,List.map_ofFn,Function.comp_id,Function.comp_def,id_eq] using h

/-- Reading all real rows changes only the placement of the time-zero records. -/
theorem chronology_perm (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) :
    (chronology input blocks).Perm (List.ofFn (rowFields input blocks)).flatten := by
  have init := flatten_input (w+1) 0 input
  simp only [Nat.zero_add] at init
  have events := congrArg (List.map (TeamProbeEmit.widenRecord (w := w))) (flatten_blocks 1 blocks)
  simp only [List.map_flatten,List.map_ofFn,Function.comp_def] at events
  unfold chronology
  rw [← init,←events]
  exact interleave _ _

private theorem physicalSlots_decode (t : ℕ) (e : Event w)
    (hf : ∀ z ∈ (eventFields t e).map widenRecord, TeamTapeSorting.ProbeFits z) :
    (physicalSlots t e).map WordRecord.record = physicalFields t e := by
  have he := TeamTapeSorting.packRow_decode ((eventFields t e).map widenRecord) hf
  rw [physicalSlots_of_decode t e _ he]
  exact he

/-- The actual bit-level block emission decodes to all and only its widened logical fields. -/
theorem historySlots_decode (t : ℕ) (es : List (Event w))
    (hf : ∀ z ∈ (historyFields t es).map widenRecord, TeamTapeSorting.ProbeFits z) :
    (historySlots t es).map WordRecord.record =
      ((historyFields t es).map widenRecord).flatMap TeamRecords.pair := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [historySlots,TeamEventRecords.historySlots,historyFields,List.map_append,List.flatMap_append]
    have hs := physicalSlots_decode t e (fun z hz => hf z (by simpa [historyFields] using Or.inl hz))
    have ht := ih (t+(1+e.action.extra)) (fun z hz => hf z (by simpa [historyFields] using Or.inr hz))
    rw [hs,ht,physicalFields]

/-- Under the word bounds each real processor's typed buffer is exactly the canonical
pair encoding of its interleaved row. -/
theorem realRows_eq_packRow (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (j : Fin r) (size : 2*(TeamTapeInputEmit.rowStart input j + (input j).length) ≤ 2^(w+1))
    (hf : ∀ z ∈ rowFields input blocks j, TeamTapeSorting.ProbeFits z) :
    realRows input blocks j = TeamTapeSorting.packRow (rowFields input blocks j) hf := by
  apply (List.map_injective_iff.mpr WordRecord.record_injective)
  rw [TeamTapeSorting.packRow_decode,realRows,List.map_append,TeamTapeInputEmit.records_decode _ size,
    historySlots_decode _ _ (fun z hz => hf z (List.mem_append_right _ hz))]
  simp only [rowFields,List.flatMap_append]

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
