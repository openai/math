import OAI.Computability.VPVNP.RAMSortedRecords

namespace OAI
/-! # One sorted-memory slot per instruction

A probe uses its instruction number as timestamp. Every other instruction has
one padding slot. This fixes the physical slot layout before the execution,
independently of where the loads and stores occur along a branch.
-/

namespace ThreeFlat.Diagonal.TraceRecordSort

open Computability.VPVNP.RAMMemory Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSort

variable {w : ℕ}

/-- A memory probe occupies the position of its instruction in the trace. -/
def eventSlot (t : ℕ) : Event w → Option (Record (Word w))
  | .read a v => some ⟨.read, a.val, v, t, 0⟩
  | .write a v => some ⟨.write, a.val, v, t, 0⟩
  | .tick | .choice _ => none

def eventSlots (t : ℕ) : List (Event w) → List (Option (Record (Word w)))
  | [] => []
  | e :: es => eventSlot t e :: eventSlots (t+1) es

@[simp] theorem length_eventSlots (t : ℕ) (es : List (Event w)) :
    (eventSlots t es).length = es.length := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih => simp [eventSlots, ih]

private def records (t : ℕ) (es : List (Event w)) :=
  (eventSlots t es).filterMap id

private theorem record_fields (t : ℕ) (es : List (Event w)) {r : Record (Word w)}
    (h : r ∈ records t es) : r.kind ≠ .init ∧ t ≤ r.startCost := by
  induction es generalizing t with
  | nil => simp [records, eventSlots] at h
  | cons e es ih =>
    cases e with
    | tick | choice =>
      have hh := ih (t+1) (by simpa [records, eventSlots, eventSlot] using h)
      exact ⟨hh.1, Nat.le_trans (Nat.le_succ _) hh.2⟩
    | read a v | write a v =>
      simp [records, eventSlots, eventSlot] at h
      rcases h with rfl | ht
      · simp
      · have hh := ih (t+1) (by simpa [records] using ht)
        exact ⟨hh.1, Nat.le_trans (Nat.le_succ _) hh.2⟩

private theorem chronological_records (t : ℕ) (es : List (Event w)) :
    Chronological (records t es) := by
  induction es generalizing t with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih (t+1)
    | read a v | write a v =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih _⟩
      intro s hs
      obtain ⟨hk, ht⟩ := record_fields _ es hs
      simp [Record.timestamp, Prod.Lex.toLex_lt_toLex, hk,
        show t < s.startCost from ht]

private theorem readsCorrect_records (t : ℕ) (es : List (Event w)) (memory : Memory w) :
    ReadsCorrect memory (records t es) ↔ Correct memory es := by
  induction es generalizing t memory with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih (t+1) memory
    | read a v =>
      have h : afterRecord memory ⟨.read, a.val, v, t, 0⟩ = memory := by
        funext i; simp [afterRecord]
      simp [records, eventSlots, eventSlot, ReadsCorrect, Correct, h, ← ih (t+1)]
    | write a v =>
      have h : afterRecord memory ⟨.write, a.val, v, t, 0⟩ = writeMemory memory a v := by
        funext i; simp [afterRecord, writeMemory, Function.update_apply]
      simp [records, eventSlots, eventSlot, ReadsCorrect, Correct, update, h, ← ih (t+1)]

/-- Header slots, followed by one slot per instruction, then vacant positions
extending the array to its prescribed power of two. -/
def raw (S d : ℕ) (header : ℕ → Word w) (es : List (Event w)) :
    List (Option (Record (Word w))) :=
  (initialRecords S header).map some ++ eventSlots 0 es ++
    List.replicate (2 ^ d - (S + es.length)) none

theorem length_raw (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fits : S + es.length ≤ 2 ^ d) : (raw S d header es).length = 2 ^ d := by
  simp [raw, initialRecords]
  omega

private theorem filter_raw (S d : ℕ) (header : ℕ → Word w) (es : List (Event w)) :
    (raw S d header es).filterMap id = initialRecords S header ++ records 0 es := by
  simp [raw, records, List.filterMap_map]

/-- Actual memory-check outputs of the bitonic sorting network on this fixed
power-of-two array. Missing inputs read the vacant slot. -/
def inputWire (S d : ℕ) (header : ℕ → Word w) (es : List (Event w)) (i : Fin (2^d)) :
    OrderedSlot (Word w) := ⟨((raw S d header es)[i.val]?).join⟩

def sorted (S d : ℕ) (header : ℕ → Word w) (es : List (Event w)) :
    List (Option (Record (Word w))) :=
  (List.ofFn (sort d true (inputWire S d header es))).map OrderedSlot.record

private theorem wire_list (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fits : S + es.length ≤ 2 ^ d) :
    (List.ofFn (inputWire S d header es)).map OrderedSlot.record = raw S d header es := by
  apply List.ext_getElem
  · simp [length_raw _ _ _ _ fits]
  intro i _ hi
  simp [inputWire, List.getElem?_eq_getElem hi]

/-- The adjacent sorted-pair checks are equivalent to every memory read
having the value prescribed by chronological execution. -/
theorem sorted_iff_correct (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (fits : S + es.length ≤ 2 ^ d) :
    PaddedCheck none (sorted S d header es) ↔ Correct (initialMemory S header) es := by
  have perm := ((sort_perm d true (inputWire S d header es)).symm).map OrderedSlot.record
  rw [wire_list S d header es fits] at perm
  have ordered : (sorted S d header es).Pairwise (fun x y => paddedKey x ≤ paddedKey y) := by
    simp only [sorted, List.pairwise_map, List.pairwise_ofFn]
    intro i j hij
    exact paddedKey_mono (sort_monotone _ _ hij.le)
  have hr : (initialRecords S header ++ records 0 es).Perm ((raw S d header es).filterMap id) := by
    rw [filter_raw]
  exact (paddedCheck_iff_readsCorrect hr perm ordered
    (chronological_records 0 es) (fun r hr => (record_fields 0 es hr).1)).trans
      (readsCorrect_records 0 es _)

end ThreeFlat.Diagonal.TraceRecordSort

end OAI
