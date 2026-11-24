import OAI.Computability.VPVNP.RAMTapeBoundaryBits
import OAI.Computability.VPVNP.RAMValidatorBoundary

/-!
# Decision of the RAM boundary tape pass

The pass retains the last physical record, including padding, and latches
every read check. Missing predecessor and successor fields are checked bit
by bit against zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

open RAMBoundary RAMMemory RAMSort

variable {w B : ℕ}

/-- Flatten the five word encodings of one physical slot into its bit stream. -/
def recordBytes (x : RawSlot w) : List Bool := (recordWords x).flatten

/-- Concatenate the physical slot encodings in block order. -/
def blockBytes (xs : List (RawSlot w)) : List Bool := xs.flatMap recordBytes

@[simp] theorem length_recordBytes (x : RawSlot w) : (recordBytes x).length = 5 * w := by
  simp [recordBytes, recordWords]
  omega

@[simp] theorem length_blockBytes (xs : List (RawSlot w)) :
    (blockBytes xs).length = xs.length * (5 * w) := by
  simp [blockBytes, List.length_flatMap]

/-- Each visited record replaces the predecessor, even after a failed check. -/
def rows (previous : RawSlot w) (records : List (RawSlot w)) (ok : Bool) : RawSlot w × Bool :=
  match records with
  | [] => (previous, ok)
  | current :: rest => rows current rest (ok && checked (foldRecord previous current))

/-- An interior send is compared with the last physical record. At either
missing edge the transmitted bits must all be zero. -/
def decision (hasPrev hasNext : Bool) (previous sent : RawSlot w)
    (records : List (RawSlot w)) : Bool :=
  let result := rows previous records (hasPrev || (recordBytes previous).all (!·))
  result.2 && if hasNext then equalChecked (foldRecord result.1 sent) else (recordBytes sent).all (!·)

private theorem rows_last (previous : RawSlot w) (records : List (RawSlot w)) (ok : Bool) :
    (rows previous records ok).1 = records.getLast?.getD previous := by
  induction records generalizing previous ok with
  | nil => rfl
  | cons current rest ih => simp [rows, ih, List.getLast?_cons]

private theorem rows_check (hw : 2 ≤ w) (previous : RawSlot w) (records : List (RawSlot w))
    (ok : Bool) :
    (rows previous records ok).2 = true ↔ ok = true ∧
      PaddedCheck (parsedSlot hw previous).record (records.map fun r ↦ (parsedSlot hw r).record) := by
  induction records generalizing previous ok with
  | nil => simp [rows, PaddedCheck]
  | cons current rest ih =>
    rw [rows, ih, Bool.and_eq_true, checked_foldRecord hw, readOK_spec, List.map_cons]
    cases h : (parsedSlot hw current).record <;> simp [PaddedCheck, and_assoc]

/-- The tape decision is the parsed-slot scan conjoined with a zero-bit
test on each missing endpoint. The raw records may use any tag or payload. -/
theorem decision_scan (hw : 2 ≤ w) (hasPrev hasNext : Bool) (previous sent : RawSlot w)
    (block : Fin B → RawSlot w) :
    decision hasPrev hasNext previous sent (List.ofFn block) =
      ((hasPrev || (recordBytes previous).all (!·)) &&
        (scan (parsedSlot hw previous).record (if hasNext then some (parsedSlot hw sent).record else none)
          (fun i ↦ (parsedSlot hw (block i)).record)).1 &&
        (hasNext || (recordBytes sent).all (!·))) := by
  cases B with
  | zero =>
    cases hasNext with
    | false =>
      change (_ && _) = (_ && true && _)
      simp [rows]
    | true =>
      change (_ && equalChecked (foldRecord previous sent)) =
        (_ && (true && (equalSlot (parsedSlot hw sent).record (parsedSlot hw previous).record).1) && true)
      apply Bool.eq_iff_iff.mpr
      simp [rows, equalChecked_foldRecord hw, equalSlot_spec]
      grind only
  | succ b =>
    have hB : 0 < b + 1 := Nat.succ_pos b
    have hlast : (List.ofFn block).getLast? = some (block ⟨(b + 1) - 1, by omega⟩) := by
      rw [List.getLast?_eq_some_getLast (mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hB)),
        List.getLast_ofFn]
    apply Bool.eq_iff_iff.mpr
    simp only [decision, Bool.and_eq_true, rows_check hw, rows_last, hlast, Option.getD_some,
      List.map_ofFn, Function.comp_def, scan_ok_iff hB]
    cases hasNext <;> simp [equalChecked_foldRecord hw, equalSlot_spec, lastSlot, and_assoc]
    grind only

end RAMTape.Boundary

end VPVNP
end Computability
end OAI
