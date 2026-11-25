import OAI.ThreeFlat.Diagonal.TraceSlotAdjacent
import OAI.ThreeFlat.Diagonal.TraceAdjacent
import OAI.ThreeFlat.Routing.SortStage

namespace OAI
/-! # Stable sorting of bounded memory events by a single binary key

The seven memory fields have fixed offsets. Putting the padding flag and
address above the time fields makes the tagged stable sort agree with the native
RAM checker. Its adjacent tests then recover chronological read consistency.
-/

noncomputable section
namespace Hierarchy.TaggedShorterHistoryOrder
open ThreeFlat Routing Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped Classical

variable {w m : ℕ}

def width (w : ℕ) : List (Fin 7) → ℕ
  | [] => 0
  | _::l => width w l+w

def pack (fields : Fin 7 → Word w) :
    (l : List (Fin 7)) → Fin (width w l) → Bool
  | [], j => Fin.elim0 j
  | i::l, j => Fin.append (pack fields l) ((addressEquiv w).symm (fields i)) j

theorem packed_lt (a b : Fin 7 → Word w) (l : List (Fin 7)) :
    addressEquiv _ (pack a l) < addressEquiv _ (pack b l) ↔ TraceSlots.keyLess a b l := by
  induction l with
  | nil =>
    have eq : pack a [] = pack b [] := funext fun i => Fin.elim0 i
    simp [eq,TraceSlots.keyLess]
  | cons i l ih =>
    change (addressEquiv _ (Fin.append (pack a l) ((addressEquiv w).symm (a i)))).val <
      (addressEquiv _ (Fin.append (pack b l) ((addressEquiv w).symm (b i)))).val ↔ _
    simp only [←wordValue_addressEquiv,wordValue_append_lt_iff,Prod.Lex.toLex_lt_toLex,
      Equiv.apply_symm_apply,ih,TraceSlots.keyLess]

abbrev RecordWidth (w : ℕ) := width w TraceSlots.keyIndices

theorem recordWidth_eq : RecordWidth w = 7*w := by
  simp [RecordWidth,TraceSlots.keyIndices,width]; omega

def bits (hw : 2≤w) (s : Option (WordRecord w)) :=
  pack (TraceSlots.fields hw s) TraceSlots.keyIndices

theorem bits_order (hw : 2≤w) (a b : Option (WordRecord w)) :
    addressEquiv _ (bits hw a) < addressEquiv _ (bits hw b) ↔ TraceSlots.toOrdered a < TraceSlots.toOrdered b :=
  (packed_lt _ _ _).trans (TraceSlots.keyLess_iff hw _ _)

def permutation (hw : 2≤w) (slots : Fin (2^m) → Option (WordRecord w)) :=
  Tuple.sort (fun i => addressEquiv _ (bits hw (slots i)))

/-- A single stable sort by the entire encoded word orders all memory fields,
regardless of how many vacant records pad the array. -/
theorem stable_equals_native (hw : 2≤w) (slots : Fin (2^m) → Option (WordRecord w)) :
    (fun i => TraceSlots.toOrdered (slots (permutation hw slots i))) =
      Computability.VPVNP.RAMSort.sort m true (fun i => TraceSlots.toOrdered (slots i)) := by
  let k := fun i => addressEquiv _ (bits hw (slots i))
  let e := permutation hw slots
  have mono : Monotone (fun i => TraceSlots.toOrdered (slots (e i))) := by
    intro i j h
    by_contra! rev
    exact ((bits_order hw _ _).mpr rev).not_ge (Tuple.monotone_sort k h)
  apply List.ofFn_injective
  have p := (e.ofFn_comp_perm (fun i => TraceSlots.toOrdered (slots i))).trans
    (Computability.VPVNP.RAMSort.sort_perm m true (fun i => TraceSlots.toOrdered (slots i))).symm
  exact p.eq_of_pairwise' mono.sortedLE_ofFn.pairwise
    (Computability.VPVNP.RAMSort.sort_monotone m (fun i => TraceSlots.toOrdered (slots i))).sortedLE_ofFn.pairwise

/-- The same row numbering is visible at the exposed output pins of the
tagged sort relation, so the scan may read its fixed field offsets. -/
theorem sort_pins (hw : 2≤w) (slots : Fin (2^m) → Option (WordRecord w)) :
    SortNetwork.sortedPins id (Function.uncurry (fun i => bits hw (slots i))) =
      Function.uncurry (fun i => bits hw (slots (permutation hw slots i))) := rfl

/-- Initial stores, probe timestamps and suffix padding are included in the
typed chronological-to-physical equality. -/
theorem scan_iff_correct (hw : 2≤w) (S : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (room : S+es.length≤2^m) (slots : Fin (2^m) → Option (WordRecord w))
    (chron : ∀ i, TraceSlots.toOrdered (slots i) = TraceRecordSort.inputWire S m header es i) :
    PaddedCheck none (List.ofFn fun i => (slots (permutation hw slots i)).map WordRecord.record) ↔
      Correct (initialMemory S header) es := by
  have eq := stable_equals_native hw slots
  rw [show (fun i => TraceSlots.toOrdered (slots i)) = TraceRecordSort.inputWire S m header es from funext chron] at eq
  have orderedRecords := congrArg (fun r : Fin (2^m) → OrderedSlot (Word w) => (List.ofFn r).map OrderedSlot.record) eq
  rw [←TraceRecordSort.sorted_iff_correct S m header es room]
  unfold TraceRecordSort.sorted
  simpa only [List.map_ofFn,Function.comp_def,TraceSlots.toOrdered] using
    (congrArg (PaddedCheck none) orderedRecords).to_iff

end Hierarchy.TaggedShorterHistoryOrder

end
end OAI
