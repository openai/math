import OAI.Hierarchy.TaggedShorterObservedMemory
import OAI.ThreeFlat.Diagonal.TraceInputSlots

namespace OAI
/-! # Fixed clock positions, including final observed output reads -/

noncomputable section
namespace Hierarchy.TaggedShorterChronology
open ThreeFlat Diagonal TraceRows
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped Classical

variable {w f u m : ℕ} {C : Type*}

def rowEvent : Row w C → Event w
  | .move _ e => e
  | _ => .tick

def events (rows : Fin f → Row w C) (addr value : Fin u → Word w) : Fin (f+u) → Event w :=
  Fin.append (rowEvent ∘ rows) (fun i => .read (addr i) (value i))

theorem pad_events (P : Program w C) {c : C} {xs : List (Row w C)} (h : Local P c xs) :
    xs.map rowEvent = (report xs).events ++ List.replicate (xs.length-(report xs).events.length) .tick := by
  induction h with
  | halt h => simp [rowEvent,report,List.replicate_succ]
  | move h rest ih => simp [rowEvent,report,Report.prepend,ih]

private theorem correct_ticks (mem : Memory w) (n : ℕ) (xs : List (Event w)) :
    Correct mem (List.replicate n .tick ++ xs) ↔ Correct mem xs := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,Correct,update,ih]

theorem correct_events (P : Program w C) {c : C} (rows : Fin f → Row w C)
    (fit : Local P c (List.ofFn rows)) (addr value : Fin u → Word w) (mem : Memory w) :
    Correct mem (List.ofFn (events rows addr value)) ↔
      Correct mem (report (List.ofFn rows)).events ∧
      ∀ i, value i=after mem (report (List.ofFn rows)).events (addr i).val := by
  have split : List.ofFn (events rows addr value) =
      (List.ofFn rows).map rowEvent ++ TaggedShorterObservedMemory.queries addr value := by
    simp [events,List.ofFn_add,TaggedShorterObservedMemory.queries,List.map_ofFn,Function.comp_def]
  rw [split,pad_events P fit,List.append_assoc,TaggedShorterObservedMemory.correct_append]
  rw [correct_ticks]
  have h := TaggedShorterObservedMemory.data_words mem (report (List.ofFn rows)).events addr value
  simpa only [TaggedShorterObservedMemory.correct_append] using h

def eventWordSlot (t : Word w) : Event w → Option (WordRecord w)
  | .read a v => some ⟨.read,a,v,t,0⟩
  | .write a v => some ⟨.write,a,v,t,0⟩
  | _ => none

theorem wordSlot_record (t : Word w) (e : Event w) :
    (eventWordSlot t e).map WordRecord.record = TraceRecordSort.eventSlot t.val e := by cases e <;> rfl

theorem wordSlot_row (t : Word w) (x : Row w C) :
    eventWordSlot t (rowEvent x)=rowWordSlot t x := by
  cases x with
  | move _ e => cases e <;> rfl
  | _ => rfl

theorem eventSlots_ofFn {n : ℕ} (t : ℕ) (e : Fin n → Event w) :
    TraceRecordSort.eventSlots t (List.ofFn e) = List.ofFn (fun i => TraceRecordSort.eventSlot (t+i.val) (e i)) := by
  induction n generalizing t with
  | zero => simp [TraceRecordSort.eventSlots]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f:=fun i=>TraceRecordSort.eventSlot (t+i.val) (e i))]
    simp [TraceRecordSort.eventSlots,ih,Nat.add_comm,Nat.add_left_comm]

def slot {n : ℕ} (S : ℕ) (hs : S≤2^w) (ht : n≤2^w) (header : ℕ → Word w) (es : Fin n → Event w) (j : ℕ) :
    Option (WordRecord w) :=
  if h : j<S then let a : Word w := ⟨j,h.trans_le hs⟩; some ⟨.init,a,header j,a,0⟩
  else if h : j-S<n then eventWordSlot ⟨j-S,h.trans_le ht⟩ (es ⟨_,h⟩) else none

theorem slot_input {n : ℕ} (S m : ℕ) (hs : S≤2^w) (ht : n≤2^w)
    (header : ℕ → Word w) (e : Fin n → Event w) (j : Fin (2^m)) :
    TraceSlots.toOrdered (slot S hs ht header e j.val)=TraceRecordSort.inputWire S m header (List.ofFn e) j := by
  apply congrArg OrderedSlot.mk
  rw [TraceRecordSort.raw,eventSlots_ofFn,List.append_assoc]
  by_cases init : j.val<S
  · rw [List.getElem?_append_left (by simpa [initialRecords] using init)]
    simp [slot,initialRecords,init,initRecord,WordRecord.record]
  · rw [List.getElem?_append_right (by simpa [initialRecords] using Nat.le_of_not_gt init)]
    simp only [List.length_map,initialRecords,List.length_range]
    by_cases timed : j.val-S<n
    · rw [List.getElem?_append_left (by simpa using timed),
        List.getElem?_eq_getElem (by simpa using timed)]
      simp [slot,init,timed,wordSlot_record]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt timed)]
      simp [slot,init,timed,List.getElem?_replicate]; split <;> rfl

end Hierarchy.TaggedShorterChronology

end
end OAI
