import OAI.ThreeFlat.Diagonal.TraceAdjacent
import OAI.ThreeFlat.Diagonal.TraceSortReplay

namespace OAI
/-! # Local sources of the paired initialization and CPU-probe slots -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP BurstRAM RAMSerialization RAMMemory RAMSort
variable {w f : ℕ} {C : Type*}

def rowSlot (t : ℕ) : Row w C → Option (Record (Word w))
  | .move _ e => TraceRecordSort.eventSlot t e
  | _ => none

private theorem rowSlots_ofFn (t : ℕ) (x : Fin f → Row w C) :
    rowSlots t (List.ofFn x) = List.ofFn fun j => rowSlot (t+j.val) (x j) := by
  induction f generalizing t with
  | zero => simp [rowSlots]
  | succ f ih =>
    rw [List.ofFn_succ, List.ofFn_succ (f := fun j => rowSlot (t+j.val) (x j))]
    change rowSlot t (x 0) :: rowSlots (t+1) (List.ofFn (fun j => x j.succ)) = _
    rw [ih]
    simp [Nat.add_left_comm, Nat.add_comm]

/-- Index calculation for a row of the addressed sort. The only data read
by an input slot are its own header word or its own CPU row. -/
def sourceSlot (S : ℕ) (header : ℕ → Word w) (xs : Fin f → Row w C) (i : ℕ) : Option (Record (Word w)) :=
  if i < S then some (initRecord header i)
  else if h : i-S < f then rowSlot (i-S) (xs ⟨i-S,h⟩) else none

/-- Source slots agree with the real bitonic input, also beyond its physical
end where the wire array is extended by empty slots. -/
theorem wire_eq_source {P : Program w C} {c : C} {xs : Fin f → Row w C} (hl : Local P c (List.ofFn xs))
    (S d : ℕ) (header : ℕ → Word w) (fit : S+f ≤ 2^d) (i : ℕ) :
    (TraceRecordSort.wire S d header (report (List.ofFn xs)).events i).record = sourceSlot S header xs i := by
  have hh := raw_eq_physical hl S d header (by simpa using fit)
  change ((TraceRecordSort.raw S d header (report (List.ofFn xs)).events)[i]?).join = _
  rw [hh, rowSlots_ofFn, List.append_assoc]
  by_cases hi : i < S
  · rw [List.getElem?_append_left (by simpa [initialRecords] using hi)]
    simp [sourceSlot, initialRecords, hi]
  · rw [List.getElem?_append_right (by simpa [initialRecords] using Nat.le_of_not_gt hi)]
    simp only [List.length_map, initialRecords, List.length_range]
    by_cases hstep : i-S < f
    · rw [List.getElem?_append_left (by simpa using hstep),
        List.getElem?_eq_getElem (by simpa using hstep)]
      simp [sourceSlot, hi, hstep]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hstep)]
      simp [sourceSlot, hi, hstep, List.getElem?_replicate]
      split <;> rfl

/-- Word-bounded form of the local probe slot. Each value is an ordinary
five-field record, and its input timestamp is the public row label. -/
def rowWordSlot (t : Word w) : Row w C → Option (WordRecord w)
  | .move _ (.read a v) => some ⟨.read,a,v,t,0⟩
  | .move _ (.write a v) => some ⟨.write,a,v,t,0⟩
  | _ => none

@[simp] theorem rowWordSlot_record (t : Word w) (x : Row w C) :
    (rowWordSlot t x).map WordRecord.record = rowSlot t.val x := by
  cases x with
  | move s e => cases e <;> rfl
  | halt | pad => rfl

/-- The supplied slot has at most one addressable header value or CPU
value. Each record has a unique representable word serialization. -/
def localWordSlot (S : ℕ) (hs : S ≤ 2^w) (ht : f ≤ 2^w) (header : ℕ → Word w)
    (xs : Fin f → Row w C) (i : ℕ) : Option (WordRecord w) :=
  if hi : i < S then
    let a : Word w := ⟨i,lt_of_lt_of_le hi hs⟩
    some ⟨.init,a,header i,a,0⟩
  else if h : i-S < f then rowWordSlot ⟨i-S,lt_of_lt_of_le h ht⟩ (xs ⟨i-S,h⟩) else none

theorem localWordSlot_widen (S : ℕ) (hs : S ≤ 2^w) (ht : f ≤ 2^w) (header : ℕ → Word w)
    (xs : Fin f → Row w C) (i : ℕ) :
    (localWordSlot S hs ht header xs i).map WordRecord.record = sourceSlot S header xs i := by
  by_cases hi : i < S
  · simp [localWordSlot, sourceSlot, hi, initRecord, WordRecord.record]
  · by_cases hstep : i-S < f <;> simp [localWordSlot, sourceSlot, hi, hstep]

end ThreeFlat.Diagonal.TraceRows

end OAI
