import OAI.Computability.NearSquareRoot.CRTTableLayerProduct

/-! # Balanced CRT stages in the order used by the serial table generator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Stage

private def labels {d : ℕ} (s : Stage d) := (s.node, s.remaining)

private theorem labels_injective {d : ℕ} : Function.Injective (labels (d := d)) := by
  intro x y h
  cases x
  cases y
  simpa [labels] using h

private def indexedRows {α : Type*} (height : ℕ) (xs : List α) :=
  (List.range height).map fun r => (CRTTree.level (height-1-r) xs).map (fun node => (node,r))

private theorem zipSame {α β γ δ : Type*} (combine : β → γ → δ) (f : α → β) (g : α → γ)
    (xs : List α) : List.zipWith combine (xs.map f) (xs.map g) =
      xs.map (fun t => combine (f t) (g t)) := by
  induction xs <;> simp [*]

private theorem projectZip {α β : Type*} (f : α → β) (l r : List (List α)) :
    (List.zipWith (· ++ ·) l r).map (List.map f) =
      List.zipWith (· ++ ·) (l.map (List.map f)) (r.map (List.map f)) := by
  induction l generalizing r with
  | nil => simp
  | cons l ls ih => cases r <;> simp [ih]

private theorem indexedRows_succ {α : Type*} (height : ℕ) (xs : List α) :
    indexedRows (height+1) xs =
      List.zipWith (· ++ ·) (indexedRows height (CRTTree.left xs))
        (indexedRows height (CRTTree.right xs)) ++ [[(xs,height)]] := by
  unfold indexedRows
  rw [List.range_succ, List.map_append, zipSame]
  simp only [List.map_cons, List.map_nil, Nat.add_sub_cancel, Nat.sub_self, CRTTree.level]
  congr 1
  apply List.map_congr_left
  intro r hr
  have h := List.mem_range.mp hr
  rw [show height - r = height - 1 - r + 1 by omega, CRTTree.level_succ_eq, List.map_append]

/-- Forgetting proof fields, each bottom-up row contains precisely the nodes
at its distance from the root in the order used to parse the packed header. -/
private theorem labels_layers {d : ℕ} (height : ℕ) (xs : List (Fin d)) (hs hc) :
    ((layers height xs hs hc).map (List.map labels)) = indexedRows height xs := by
  induction height generalizing xs with
  | zero => rfl
  | succ height ih =>
    rw [layers, List.map_append, projectZip, ih, ih, indexedRows_succ]
    rfl

/-- Name the exact row of executable stages by its distance from the root. -/
def atDepth (d n : ℕ) (hn : n < Nat.clog 2 d) : List (Stage d) :=
  (List.finRange (CRTTree.level n (List.finRange d)).length).map (atLevel d n hn)

theorem getElem_atDepth (d n : ℕ) (hn : n < Nat.clog 2 d)
    (j : Fin (CRTTree.level n (List.finRange d)).length) :
    (atDepth d n hn)[j.val]'(by simp [atDepth]) = atLevel d n hn j := by
  simp [atDepth]

private theorem labels_atDepth (d n : ℕ) (hn : n < Nat.clog 2 d) :
    (atDepth d n hn).map labels = (CRTTree.level n (List.finRange d)).map
      (fun node => (node,Nat.clog 2 d - 1 - n)) := by
  apply List.ext_getElem
  · simp [atDepth]
  · intro r hr hs
    simp [atDepth, atLevel, labels, Nat.sub_sub, Nat.add_comm]

/-- The indexed table rows are the same rows whose sequential product
realizes the original padded permutation. -/
theorem fullLayers_getElem (d n : ℕ) (hn : n < Nat.clog 2 d) :
    let height := Nat.clog 2 d
    let rows := layers height (List.finRange d) (List.sortedLT_finRange d).pairwise
      (by simpa using Nat.le_pow_clog (by decide : 1 < 2) d)
    rows[height-1-n]?.getD [] = atDepth d n hn := by
  let h := Nat.clog 2 d
  let xs := List.finRange d
  let hs := (List.sortedLT_finRange d).pairwise
  have hc : xs.length ≤ 2^h := by simpa [xs,h] using Nat.le_pow_clog (by decide : 1 < 2) d
  let rows := layers h xs hs hc
  let r := h-1-n
  have hr : r < h := by dsimp [r,h]; omega
  have hinner : h-1-r = n := by dsimp [h,r]; omega
  have hr' : r < rows.length := by simpa [rows] using hr
  have eqv := congrArg (fun out => out[r]?) (labels_layers h xs hs hc)
  change ((rows.map (List.map labels))[r]?) = _ at eqv
  simp only [indexedRows, List.getElem?_map, List.getElem?_eq_getElem hr',
    List.getElem?_eq_getElem (show r < (List.range h).length by simpa using hr),
    Option.map_some, List.getElem_range, Option.some.injEq, hinner] at eqv
  dsimp only
  change rows[r]?.getD [] = atDepth d n hn
  rw [List.getElem?_eq_getElem hr']
  apply labels_injective.list_map
  exact eqv.trans (labels_atDepth d n hn).symm

end CRTTable.Stage

end NearSquareRoot
end Computability
end OAI
