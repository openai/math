import OAI.ThreeFlat.Diagonal.TraceRows
import OAI.ThreeFlat.Diagonal.TraceRecordSort

namespace OAI
/-! # Adjacent constraints of the register and memory traces -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM

variable {w : ℕ} {C : Type*}

def before : Row w C → Option C
  | .move c _ | .halt c _ => some c
  | .pad => none

/-- Pairwise transition check, using a final padding row as the right boundary. -/
def pair (P : Program w C) : Row w C → Row w C → Prop
  | .move c e, y => ∃ d, next? (P.step c) e = some d ∧ before y = some d
  | .halt c out, y => P.step c = .finish out ∧ y = .pad
  | .pad, y => y = .pad

/-- Check each adjacent pair, including the right boundary after the last
physical row. -/
def pairs (P : Program w C) : List (Row w C) → Prop
  | [] => True
  | x :: xs => pair P x (xs.headD .pad) ∧ pairs P xs

private theorem head_before {P : Program w C} {c rows} (h : Local P c rows) :
    before (rows.headD .pad) = some c := by cases h <;> rfl

private theorem padding_pairs (P : Program w C) (f : ℕ) :
    pairs P (List.replicate f (.pad : Row w C)) := by
  induction f with
  | zero => trivial
  | succ f ih =>
    rw [List.replicate_succ]
    refine ⟨?_, ih⟩
    cases f <;> rfl

private theorem of_padding_head (P : Program w C) (rows : List (Row w C))
    (hh : rows.headD .pad = .pad) (hp : pairs P rows) :
    rows = List.replicate rows.length .pad := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    change x = .pad at hh
    subst x
    obtain ⟨ht, hl⟩ := hp
    simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons .pad) (ih ht hl)

/-- The only across-time register conditions are comparisons to the next
row and the fixed initial register condition. -/
theorem local_iff_pairs (P : Program w C) (c : C) (rows : List (Row w C)) :
    Local P c rows ↔ before (rows.headD .pad) = some c ∧ pairs P rows := by
  constructor
  · intro h
    refine ⟨head_before h, ?_⟩
    induction h with
    | @halt c f out hs =>
      refine ⟨⟨hs, ?_⟩, padding_pairs P f⟩
      cases f <;> rfl
    | move hs ht ih => exact ⟨⟨_, hs, head_before ht⟩, ih⟩
  · induction rows generalizing c with
    | nil => simp [before]
    | cons x xs ih =>
      intro ⟨hfirst, hpair, htail⟩
      cases x with
      | pad => simp [before] at hfirst
      | move c' e =>
        have he : c' = c := Option.some.inj hfirst
        subst c'
        obtain ⟨d, hs, hn⟩ := hpair
        exact .move hs (ih d ⟨hn, htail⟩)
      | halt c' out =>
        have he : c' = c := Option.some.inj hfirst
        subst c'
        obtain ⟨hs, hj⟩ := hpair
        rw [of_padding_head P xs hj htail]
        exact .halt hs

/-- Fixed one-slot-per-row representation, including the halt and trailing
padding positions. -/
def rowSlots (t : ℕ) : List (Row w C) → List (Option (Computability.VPVNP.RAMMemory.Record (Word w)))
  | [] => []
  | x :: xs =>
    (match x with
    | .move _ e => TraceRecordSort.eventSlot t e
    | _ => none) :: rowSlots (t+1) xs

private theorem rowSlots_pad (t f : ℕ) :
    rowSlots t (List.replicate f (.pad : Row w C)) = List.replicate f none := by
  induction f generalizing t with
  | zero => rfl
  | succ f ih => simp only [List.replicate_succ, rowSlots, ih]

theorem rowSlots_eq {P : Program w C} {c rows} (h : Local P c rows) (t : ℕ) :
    rowSlots t rows = TraceRecordSort.eventSlots t (report rows).events ++
      List.replicate (rows.length - (report rows).events.length) none := by
  induction h generalizing t with
  | halt hs => simp [rowSlots, report, TraceRecordSort.eventSlots, rowSlots_pad, List.replicate_succ]
  | move hs ht ih => simp [rowSlots, report, Report.prepend, TraceRecordSort.eventSlots, ih]

/-- Populate the fixed array using local CPU rows. Its slot values agree
with the chronological report in all physically used and vacant positions. -/
theorem raw_eq_physical {P : Program w C} {c rows} (h : Local P c rows)
    (S d : ℕ) (header : ℕ → Word w) (fits : S + rows.length ≤ 2 ^ d) :
    TraceRecordSort.raw S d header (report rows).events =
      (Computability.VPVNP.RAMMemory.initialRecords S header).map some ++ rowSlots 0 rows ++
        List.replicate (2 ^ d - (S + rows.length)) none := by
  rw [rowSlots_eq h]
  have hlen := (local_spec h).1.length_lt
  simp only [TraceRecordSort.raw, List.append_assoc, ← List.replicate_add]
  congr 3; omega

end ThreeFlat.Diagonal.TraceRows

end OAI
