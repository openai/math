import OAI.Computability.NearSquareRoot.CRTTablePrefix

/-! # Computing the prefix reader's position fields from the padded widths

The input lists axes in increasing significance. A field's absolute MSF offset
is the sum of the widths of the axes following it. The balanced-tree split is
applied to these annotated fields to select the external reader's positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

/-- The width of one field paired with its absolute MSF offset. -/
private def locate (p : List ControlAxis × Tally) : ControlAxis :=
  ((Iter.pick ([],[]) p).1, (((cutLists (()::p.2,p.1)).2).map Prod.fst).flatten)

private theorem locate_easy : Easy locate := by
  have tail : Easy (fun p : List ControlAxis × Tally => (cutLists (()::p.2,p.1)).2) :=
    (easy_cut (g := fun p : List ControlAxis × Tally => (()::p.2,p.1)) (by fun_prop)).sndCompose
  exact (Iter.facile ([],[])).fstCompose.pair (tail.compose Easy.fst.mapping |>.compose Easy.flatten)

private def located (xs : List ControlAxis) : List ControlAxis :=
  polyPush locate (xs, Iter.lineup (ruler xs))

private theorem located_poly : Poly located :=
  (Poly.identity.pair ((Easy.ruler Easy.identity).poly.compose Iter.poly_line)).compose
    (Poly.push [] [] locate_easy.poly)

private def positionRow (d : ControlAxis) : List Tally :=
  polyPush (fun p : Tally × Tally => p.1 ++ p.2) (d.2,Iter.lineup d.1)

private theorem positionRow_poly : Poly positionRow :=
  (Easy.snd.poly.pair (Easy.fst.poly.compose Iter.poly_line)).compose
    (Poly.push [] [] (show Easy (fun p : Tally × Tally => p.1 ++ p.2) by fun_prop).poly)

/-- One row per padded axis in increasing significance, with positions in
MSF order inside each row. -/
def positionFields (xs : List ControlAxis) : List (List Tally) :=
  (located xs).map positionRow

theorem positionFields_poly : Poly positionFields :=
  located_poly.compose (Poly.maps positionRow positionRow_poly)

/-- Absolute positions read for the external setting at the requested level,
from the most significant selected field to the least significant one. -/
def externalPositions (q : Tally × List ControlAxis) : List Tally :=
  (((levelBlocks (q.1,located q.2)).map Prod.fst).flatten.reverse.map positionRow).flatten

theorem externalPositions_poly : Poly externalPositions :=
  (((Easy.fst.poly.pair (Easy.snd.poly.compose located_poly)).compose levelBlocks_poly).compose
    (Easy.fst.mapping.compose Easy.flatten |>.compose Easy.reverse).poly).compose
      ((Poly.maps positionRow positionRow_poly).compose Easy.flatten.poly)

variable {α : Type*} [DecidableEq α]

private theorem fieldOffset_append (width : α → ℕ) (xs ys : List α) (i : α) :
    fieldOffset width (xs ++ ys) i = if i ∈ xs then fieldOffset width xs i else
      (xs.map width).sum + fieldOffset width ys i := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = i
    · subst x
      simp [fieldOffset]
    · by_cases hm : i ∈ xs <;> simp [fieldOffset, h, Ne.symm h, hm, ih, Nat.add_assoc]

private theorem fieldOffset_suffix (width : α → ℕ) (xs : List α) (hn : xs.Nodup) (j : ℕ)
    (hj : j < xs.length) :
    fieldOffset width xs.reverse xs[j] = ((xs.drop (j+1)).map width).sum := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hn
    cases j with
    | zero => simp [fieldOffset_append, hx, fieldOffset, List.map_reverse]
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      simpa [List.reverse_cons, fieldOffset_append, List.getElem_mem] using ih hxs j hj'

private def fieldDesc (width : α → ℕ) (xs : List α) (i : α) : ControlAxis :=
  (tally (width i), tally (fieldOffset width xs.reverse i))

private theorem located_spec (width : α → ℕ) (xs : List α) (hn : xs.Nodup)
    (desc : α → ControlAxis) (hw : ∀ i ∈ xs, (desc i).1.length = width i) :
    located (xs.map desc) = xs.map (fieldDesc width xs) := by
  apply List.ext_getElem
  · simp [located, polyPush]
  · intro j h₁ h₂
    have hj : j < xs.length := by simpa using h₂
    simp only [located, polyPush, Iter.lineup, List.getElem_map, List.getElem_ofFn, locate,
      Iter.search (xs.map desc) ([],[]) j (by simpa using hj), cutLists, List.length_cons, tally_length,
      fieldDesc]
    apply Prod.ext
    · exact (recover_tally _).symm.trans (congrArg tally (hw _ (List.getElem_mem hj)))
    · dsimp only
      rw [← recover_tally (((xs.map desc).drop (j+1)).map Prod.fst).flatten,
        fieldOffset_suffix width xs hn j hj]
      congr 1
      simp only [List.length_flatten, List.map_map, ← List.map_drop]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      exact hw i (List.mem_of_mem_drop hi)

private theorem positionRow_spec (width : α → ℕ) (xs : List α) (i : α) :
    positionRow (fieldDesc width xs i) =
      List.ofFn (fun k => tally (fieldPosition width xs i k)) := by
  simp only [positionRow, fieldDesc, Iter.lined, polyPush, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  rw [← recover_tally (tally (fieldOffset width xs.reverse i) ++ tally k.val)]
  simp [fieldPosition]

theorem positionFields_spec (width : α → ℕ) (xs : List α) (hn : xs.Nodup)
    (desc : α → ControlAxis) (hw : ∀ i ∈ xs, (desc i).1.length = width i) :
    positionFields (xs.map desc) = xs.map (fun i =>
      List.ofFn (fun k => tally (fieldPosition width xs i k))) := by
  simp only [positionFields, located_spec width xs hn desc hw, List.map_map, Function.comp_def,
    positionRow_spec]

theorem externalPositions_spec (width : α → ℕ) (xs : List α) (hx : xs.Nodup)
    (desc : α → ControlAxis) (hw : ∀ i ∈ xs, (desc i).1.length = width i)
    (n : ℕ) (hn : n ≤ Nat.clog 2 xs.length) :
    externalPositions (tally n, xs.map desc) = levelPositions width xs n := by
  rw [externalPositions, located_spec width xs hx desc hw, levelBlocks_eq _ _ (by simpa using hn)]
  simp only [List.map_map, Function.comp_def, ← List.flatMap_def]
  change (((CRTTree.controls n (xs.map (fieldDesc width xs))).reverse.map positionRow).flatten) = _
  simp [CRTTree.controls_map, levelPositions, selectionPositions, List.map_reverse, List.map_map,
    List.flatMap_def, Function.comp_def, positionRow_spec]

end CRTTable

end NearSquareRoot
end Computability
end OAI
