import OAI.Computability.NearSquareRoot.CRTTableAxes
import OAI.Computability.NearSquareRoot.CRTTableLevel

/-! # Enumerating the target blocks of a CRT stage on the coded machine -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

private def indexed {X : Type} (blank : X) (xs : List X) : List (Tally × X) :=
  zipFair [] blank (Iter.lineup (ruler xs),xs)

private theorem indexed_poly {X : Type} [Codec X] (blank : X) : Poly (indexed blank) := by
  exact (((Easy.ruler (Easy.identity (X := List X))).poly.compose Iter.poly_line).pair Poly.identity).compose
    (easy_zip [] blank).poly

private theorem indexed_map {X Y : Type} (blank : Y) (xs : List X) (f : X → Y) :
    indexed blank (xs.map f) =
      (List.finRange xs.length).map (fun j => (tally j.val,f xs[j.val])) := by
  rw [indexed,zipFair_eq_zip _ _ _ _ (by simp)]
  apply List.ext_getElem <;> simp [Iter.lineup]

private def ids (xs : List ControlAxis) : List ControlAxis :=
  (Iter.lineup (ruler xs)).map (fun j => (j,([] : Tally)))

private theorem ids_poly : Poly ids := by
  exact ((Easy.ruler (Easy.identity (X := List ControlAxis))).poly.compose Iter.poly_line).compose
    (Poly.maps _ (show Poly (fun j : Tally => (j,([] : Tally))) by fun_prop))

private theorem ids_eq (xs : List ControlAxis) :
    ids xs = (List.finRange xs.length).map (fun j => (tally j.val,([] : Tally))) := by
  apply List.ext_getElem <;> simp [ids,Iter.lineup]

abbrev Slot := (Tally × Tally) × Tally

private def nodeSlots (s : Tally × LevelBlock) : List Slot :=
  polyPush (fun p : Tally × (Tally × ControlAxis) => ((p.1,p.2.1),p.2.2.1))
    (s.1,indexed ([],[]) s.2.2)

private theorem nodeSlots_poly : Poly nodeSlots := by
  have body : Poly (fun p : Tally × (Tally × ControlAxis) => ((p.1,p.2.1),p.2.2.1)) := by fun_prop
  have indexed' := (show Poly (fun p : Tally × LevelBlock => p.2.2) by fun_prop).compose
    (indexed_poly (([],[]) : ControlAxis))
  exact (Easy.fst.poly.pair indexed').compose (Poly.push [] ([],[],[]) body)

/-- Enumerate node, target offset within that node, and global axis number.
Every number in the output is represented by an actual unary index. -/
def targetListing (p : Tally × List ControlAxis) : List Slot :=
  (indexed ([],[]) (levelBlocks (p.1,ids p.2))).flatMap nodeSlots

theorem targetListing_poly : Poly targetListing := by
  have nodes := (Easy.fst.poly.pair (Easy.snd.poly.compose ids_poly)).compose levelBlocks_poly
  exact ((nodes.compose (indexed_poly (([],[]) : LevelBlock))).compose
    (Poly.maps nodeSlots nodeSlots_poly)).compose Easy.flatten.poly

/-- The exact finite indices corresponding to the order on the output tape. -/
def targetOrder (d n : ℕ) : List (TargetIndex d n) :=
  (List.finRange (CRTTree.level n (List.finRange d)).length).sigma
    (fun j => List.finRange (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val])).length)

theorem targetOrder_nodup (d n : ℕ) : (targetOrder d n).Nodup :=
  (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

theorem targetOrder_complete (d n : ℕ) (b : TargetIndex d n) : b ∈ targetOrder d n := by
  rcases b with ⟨j,i⟩
  simp [targetOrder]

noncomputable def targetRank (d n : ℕ) : Fin (targetOrder d n).length ≃ TargetIndex d n :=
  Equiv.ofBijective (targetOrder d n).get ⟨(targetOrder_nodup d n).injective_get, fun b =>
    List.mem_iff_get.mp (targetOrder_complete d n b)⟩

private theorem level_ids (d n : ℕ) (hn : n ≤ Nat.clog 2 d) :
    let f := fun j : Fin d => (tally j.val,([] : Tally))
    levelBlocks (tally n,(List.finRange d).map f) = (CRTTree.level n (List.finRange d)).map
      (fun z => ((CRTTree.left z).map f,(CRTTree.right z).map f)) := by
  dsimp only
  rw [levelBlocks_eq _ _ (by simpa using hn), CRTTree.level_map]
  simp [List.map_map, Function.comp_def, CRTTree.left, CRTTree.right]

abbrev slotOf {d n : ℕ} (b : TargetIndex d n) : Slot :=
  ((tally b.1.val,tally b.2.val),tally (targetAxis d n b).val)

theorem targetListing_eq (xs : List ControlAxis) (n : ℕ) (hn : n ≤ Nat.clog 2 xs.length) :
    targetListing (tally n,xs) = (targetOrder xs.length n).map slotOf := by
  simp only [targetListing,ids_eq,level_ids _ _ hn,indexed_map,List.flatMap_map]
  unfold targetOrder List.sigma
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  simp [nodeSlots,polyPush,indexed_map,List.map_map,Function.comp_def,targetAxis]

end CRTTable

end NearSquareRoot
end Computability
end OAI
