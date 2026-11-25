import OAI.Computability.NearSquareRoot.CRTTableControlPacking
import OAI.Computability.NearSquareRoot.CRTControlledBenesMask

/-! # Projecting the CRT controls from the most-significant-first prefix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

variable {α : Type*}

/-- Count the bits before the first occurrence of an axis in MSF order. -/
def fieldOffset [DecidableEq α] (width : α → ℕ) : List α → α → ℕ
  | [], _ => 0
  | i :: is, j => if i = j then 0 else width i + fieldOffset width is j

/-- Position of a bit in the full address. Axes are given in increasing
significance and bit indices within an axis are in MSF order. -/
def fieldPosition [DecidableEq α] (width : α → ℕ) (axes : List α) (i : α) (k : Fin (width i)) : ℕ :=
  fieldOffset width axes.reverse i + k.val

private theorem offset_lt [DecidableEq α] (width : α → ℕ) (axes : List α) (i : α)
    (hi : i ∈ axes) (k : Fin (width i)) :
    fieldOffset width axes i + k.val < (axes.map width).sum := by
  induction axes with
  | nil => cases hi
  | cons j js ih =>
    by_cases he : j = i
    · subst j
      simp only [fieldOffset, ↓reduceIte, Nat.zero_add, List.map_cons, List.sum_cons]
      omega
    · have h := ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he))
      simp only [fieldOffset, he, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

theorem fieldPosition_lt [DecidableEq α] (width : α → ℕ) (axes : List α) (i : α)
    (hi : i ∈ axes) (k : Fin (width i)) : fieldPosition width axes i k < (axes.map width).sum := by
  simpa [fieldPosition, List.map_reverse] using offset_lt width axes.reverse i (by simpa using hi) k

/-- Unary prefix coordinates for a collection of control fields, emitted
from the highest selected axis to the lowest. -/
def selectionPositions (width : α → ℕ) (pos : (i : α) → Fin (width i) → ℕ)
    (selected : List α) : List Tally :=
  selected.reverse.flatMap fun i => List.ofFn fun k => tally (pos i k)

/-- Positions consumed by the external-control reader at a balanced-tree depth. -/
def levelPositions [DecidableEq α] (width : α → ℕ) (axes : List α) (n : ℕ) : List Tally :=
  selectionPositions width (fieldPosition width axes) (CRTTree.controls n axes)

private theorem readIndex (z : List Bool) (n : ℕ) :
    Benes.prefixBit (z,tally n) = z[n]?.getD false := by
  rw [← List.head?_drop, Benes.prefixBit, tally_length]
  cases z.drop n <;> rfl

private theorem getField [DecidableEq α] (width : α → ℕ) (bits : α → List Bool)
    (axes : List α) (hw : ∀ i ∈ axes, (bits i).length = width i)
    (j : α) (hj : j ∈ axes) (k : Fin (width j)) :
    (axes.flatMap bits)[fieldOffset width axes j + k.val]? = some ((bits j)[k.val]'(by rw [hw j hj]; exact k.isLt)) := by
  induction axes with
  | nil => cases hj
  | cons i is ih =>
    have hi := hw i (by simp)
    simp only [List.flatMap_cons, fieldOffset]
    by_cases he : i = j
    · subst i
      simp only [Nat.zero_add, ↓reduceIte]
      rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem]
    · have hj' : j ∈ is := (List.mem_cons.mp hj).resolve_left (Ne.symm he)
      simp only [he, ↓reduceIte]
      rw [Nat.add_assoc, ← hi, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih (fun s hs => hw s (List.mem_cons_of_mem _ hs)) hj'

/-- Reading a natural-order coordinate from the complete prefix retrieves the
corresponding MSF bit of that axis. -/
theorem fieldPosition_bit [DecidableEq α] (width : α → ℕ) (axes : List α) (bits : α → List Bool)
    (hw : ∀ i ∈ axes, (bits i).length = width i) (i : α) (hi : i ∈ axes) (k : Fin (width i)) :
    Benes.prefixBit (packFields bits axes,tally (fieldPosition width axes i k)) =
      (bits i)[k.val]'(by rw [hw i hi]; exact k.isLt) := by
  rw [readIndex]
  have h := getField width bits axes.reverse (fun j hj => hw j (by simpa using hj)) i
    (by simpa using hi) k
  simp only [packFields, fieldPosition, h, Option.getD_some]

theorem prefixWordAt_fieldPosition [DecidableEq α] (width : α → ℕ) (axes : List α) (bits : α → List Bool)
    (hw : ∀ i ∈ axes, (bits i).length = width i) (i : α) (hi : i ∈ axes) :
    List.ofFn (Benes.prefixWordAt (fieldPosition width axes i) (packFields bits axes)) = bits i := by
  apply List.ext_getElem
  · simpa using (hw i hi).symm
  · intro j h₁ h₂
    exact (List.getElem_ofFn ..).trans (fieldPosition_bit width axes bits hw i hi _)

/-- This applies to any prepared layout: only the selected axis fields need
to be recoverable at the given prefix coordinates. -/
theorem prefixBits_selectionPositions (width : α → ℕ) (pos : (i : α) → Fin (width i) → ℕ)
    (selected : List α) (z : List Bool) (bits : α → List Bool)
    (h : ∀ i ∈ selected, List.ofFn (Benes.prefixWordAt (pos i) z) = bits i) :
    Benes.prefixBits (z,selectionPositions width pos selected) = packFields bits selected := by
  unfold Benes.prefixBits selectionPositions packFields
  rw [List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  rw [List.map_ofFn]
  exact h i (by simpa using hi)

theorem prefixBits_fieldPositions [DecidableEq α] (width : α → ℕ) (axes selected : List α)
    (bits : α → List Bool) (hw : ∀ i ∈ axes, (bits i).length = width i) (hsel : selected ⊆ axes) :
    Benes.prefixBits (packFields bits axes,selectionPositions width (fieldPosition width axes) selected) =
      packFields bits selected :=
  prefixBits_selectionPositions _ _ _ _ _ fun i hi => prefixWordAt_fieldPosition _ _ _ hw i (hsel hi)

/-- The controls read from the full MSF address agree with exactly the raw
header passed to the level table generator. -/
theorem prefixBits_levelPositions [DecidableEq α] (width : α → ℕ) (axes : List α) (bits : α → List Bool)
    (hw : ∀ i ∈ axes, (bits i).length = width i) (n : ℕ) :
    Benes.prefixBits (packFields bits axes,levelPositions width axes n) = packedControl n axes bits :=
  prefixBits_selectionPositions _ _ _ _ _ fun i hi =>
    prefixWordAt_fieldPosition _ _ _ hw i ((CRTTree.controls_sublist n axes).subset hi)

/-- Relabeling natural indices by physical positions preserves a control word
when the prepared prefix carries the same bit at each selected position. -/
theorem prefixBits_transport (original prepared : List Bool) (outer : List Tally) (relocate : ℕ → ℕ)
    (h : ∀ k ∈ outer, Benes.prefixBit (prepared,tally (relocate k.length)) = Benes.prefixBit (original,k)) :
    Benes.prefixBits (prepared,outer.map (fun k => tally (relocate k.length))) =
      Benes.prefixBits (original,outer) := by
  exact (List.map_map ..).trans (List.map_congr_left h)

end CRTTable

end NearSquareRoot
end Computability
end OAI
