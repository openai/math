import OAI.Computability.BorderVNP.TeamTapeInputEmit

/-! # Reassembling time-zero records across processor input segments

The start address of a processor is the sum of preceding header lengths. Empty
headers contribute no records. Joining the separate read/write buffers in address order
therefore gives exactly the initialization prefix of the global chronological transcript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputEmit

open VPVNP BurstRAM RAMSerialization

/-- A split in the bit stream gives a split between whole read/write pairs. -/
theorem records_append (w a : ℕ) (first second : List Bool) :
    records w a (first ++ second) =
      records w a first ++ records w (a+first.length) second := by
  induction first generalizing a with
  | nil => simp [records]
  | cons b bs ih =>
    simp only [List.cons_append, records, List.length_cons, ih]
    rw [show a+1+bs.length = a+(bs.length+1) by omega]

/-- Successive physical record segments, concatenated in processor order. -/
def chunkRecords (w : ℕ) : ℕ → List (List Bool) → List (WordRecord w)
  | _, [] => []
  | a, chunk :: rest => records w a chunk ++ chunkRecords w (a+chunk.length) rest

/-- The local buffers use the same absolute addresses as the unsplit global input. -/
theorem chunkRecords_eq (w a : ℕ) (chunks : List (List Bool)) :
    chunkRecords w a chunks = records w a chunks.flatten := by
  induction chunks generalizing a with
  | nil => rfl
  | cons _ _ ih => simp only [chunkRecords, List.flatten_cons, records_append, ih]

private theorem probes_ofFn (w a n : ℕ) (f : Fin n → Bool) :
    probes w a (List.ofFn f) = List.ofFn (fun i : Fin n => probe w (a+i.val) (f i)) := by
  induction n generalizing a with
  | zero => simp [probes]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [probes, Fin.val_zero, Nat.add_zero, Fin.val_succ, ih]
    apply congrArg (_ :: ·)
    apply congrArg List.ofFn
    funext i
    rw [show a+1+i.val = a+(i.val+1) by omega]

/-- Absolute start of row `i`, after all physically preceding header bits. -/
def rowStart {n : ℕ} (chunks : Fin n → List Bool) (i : Fin n) : ℕ :=
  ((List.ofFn chunks).take i.val).flatten.length

/-- Reassemble the fixed finite site banks using each row's explicit public start address. -/
theorem chunkRecords_ofFn (w a n : ℕ) (chunks : Fin n → List Bool) :
    chunkRecords w a (List.ofFn chunks) =
      (List.ofFn fun i => records w (a+rowStart chunks i) (chunks i)).flatten := by
  induction n generalizing a with
  | zero => simp [chunkRecords]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, chunkRecords, List.flatten_cons, ih]
    simp [rowStart, List.ofFn_succ, Nat.add_assoc]

/-- Memory on time-zero input words, extended by zero past the prescribed header. -/
def headerWord (w : ℕ) (bs : List Bool) (i : ℕ) : Word w :=
  word w (bs[i]?.getD false).toNat

/-- The four-word probes reconstructed from the local header bits are precisely the
records of the paper's time-zero initialization accesses from zero memory. -/
theorem probes_initialization (w : ℕ) (bs : List Bool) :
    probes w 0 bs = TeamRecords.transcript (fun _ => 0)
      (TeamRecords.initialization bs.length (headerWord w bs)) := by
  have h := TeamRecords.transcript_initialization bs.length (headerWord w bs) []
  simp only [List.append_nil, TeamRecords.transcript] at h
  have enumerated := probes_ofFn w 0 bs.length (fun i => bs[i.val])
  rw [List.ofFn_getElem] at enumerated
  rw [h, enumerated]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < bs.length := by simpa using hi
    simp [probe, headerWord, List.getElem?_eq_getElem hi']

/-- Joining independently emitted buffers gives the exact read/write expansion of the
global time-zero initialization. All later instructions may start from this same memory. -/
theorem chunkRecords_decode {w : ℕ} (chunks : List (List Bool))
    (fit : 2*chunks.flatten.length ≤ 2^w) :
    (chunkRecords w 0 chunks).map WordRecord.record =
      (TeamRecords.transcript (fun _ => 0) (TeamRecords.initialization chunks.flatten.length
        (headerWord w chunks.flatten))).flatMap TeamRecords.pair := by
  rw [chunkRecords_eq, records_decode _ (by simpa using fit), probes_initialization]

/-- Reading all processor rows in order yields the exact paired initialization records
from the single flattened input header. -/
theorem rows_decode {w n : ℕ} (chunks : Fin n → List Bool)
    (fit : 2*(List.ofFn chunks).flatten.length ≤ 2^w) :
    ((List.ofFn fun i => records w (rowStart chunks i) (chunks i)).flatten).map WordRecord.record =
      (TeamRecords.transcript (fun _ => 0) (TeamRecords.initialization (List.ofFn chunks).flatten.length
        (headerWord w (List.ofFn chunks).flatten))).flatMap TeamRecords.pair := by
  have eq := chunkRecords_ofFn w 0 n chunks
  simp only [Nat.zero_add] at eq
  rw [← eq]
  exact chunkRecords_decode _ fit

end TeamTapeInputEmit

end BorderVNP
end Computability
end OAI
