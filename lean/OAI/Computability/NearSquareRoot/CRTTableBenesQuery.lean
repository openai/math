import OAI.Computability.NearSquareRoot.CRTTableWordRows
import OAI.Computability.NearSquareRoot.CRTTableLevelEntry

/-! # CRT queries for the block Beneš switch compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- Node number and target number, followed by direction, depth and the
complete ordered box descriptors. A batch fixes this tag and varies only
the external control bits. -/
abbrev TargetTag := (Tally × Tally) × Bool × Tally × List ControlAxis

def targetDescriptor (t : TargetTag) : ControlAxis :=
  let nodes := levelBlocks t.2.2
  let node := Iter.pick ([],[]) (nodes,t.1.1)
  Iter.pick ([],[]) (node.2,t.1.2)

private theorem targetDescriptor_poly : Poly targetDescriptor := by
  have blocks := (show Poly (fun t : TargetTag => t.2.2) by fun_prop).compose levelBlocks_poly
  have node := (blocks.pair (show Poly (fun t : TargetTag => t.1.1) by fun_prop)).compose
    (Iter.facile (([],[]) : LevelBlock)).poly
  exact ((node.compose Easy.snd.poly).pair (show Poly (fun t : TargetTag => t.1.2) by fun_prop)).compose
    (Iter.facile (([],[]) : ControlAxis)).poly

def selectTarget (p : (Tally × Tally) × List (List (List Tally))) : List Tally :=
  Iter.pick [] (Iter.pick [] (p.2,p.1.1),p.1.2)

private theorem selectTarget_easy : Easy selectTarget := by
  let X := (Tally × Tally) × List (List (List Tally))
  have node := (show Easy (fun p : X => (p.2,p.1.1)) by fun_prop).compose
    (Iter.facile ([] : List (List Tally)))
  exact (node.pair (show Easy (fun p : X => p.1.2) by fun_prop)).compose
    (Iter.facile ([] : List Tally))

private theorem selectTarget_eq (t : List (List (List Tally))) (j i : ℕ) :
    selectTarget ((tally j,tally i),t) = ((t[j]?.getD [])[i]?).getD [] := by
  simp [selectTarget,Iter.pick,List.headD_eq_head?_getD,List.head?_drop]

/-- Direct polynomial-time input to the block compiler. The two entries of
every output row are equally wide MSF words. -/
def targetWordRows (p : TargetTag × List Bool) : Benes.RawTable :=
  wordRows ((targetDescriptor p.1).1,
    selectTarget (p.1.1,levelTables (p.1.2.1,p.1.2.2.1,p.1.2.2.2,p.2)))

theorem targetWordRows_poly : Poly targetWordRows := by
  let X := TargetTag × List Bool
  have tables := (show Poly (fun p : X => (p.1.2.1,p.1.2.2.1,p.1.2.2.2,p.2)) by fun_prop).compose
    levelTables_poly
  have target := ((show Poly (fun p : X => p.1.1) by fun_prop).pair tables).compose selectTarget_easy.poly
  have width := ((Easy.fst (X := TargetTag) (Y := List Bool)).poly.compose targetDescriptor_poly).compose
    Easy.fst.poly
  exact (width.pair target).compose wordRows_poly

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g-a g))

def tagAt (n j i : ℕ) (inv : Bool) : TargetTag :=
  ((tally j,tally i),inv,tally n,(List.finRange d).map (descriptor a w))

private theorem targetDescriptor_at (n : ℕ) (hn : n ≤ Nat.clog 2 d)
    (j : Fin (CRTTree.level n (List.finRange d)).length)
    (i : Fin (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val])).length)
    (inv : Bool) :
    targetDescriptor (tagAt a w n j.val i.val inv) =
      descriptor a w ((CRTTree.right ((CRTTree.level n (List.finRange d))[j.val]))[i.val]) := by
  let nodes := CRTTree.level n (List.finRange d)
  let desc := descriptor a w
  let block (z : List (Fin d)) := ((CRTTree.left z).map desc,(CRTTree.right z).map desc)
  have blocks : levelBlocks (tally n,(List.finRange d).map desc) = nodes.map block := by
    rw [levelBlocks_eq _ n (by simpa using hn), CRTTree.level_map]
    simp [nodes,block, List.map_map, Function.comp_def, CRTTree.left, CRTTree.right]
  change Iter.pick ([],[]) ((Iter.pick ([],[])
    (levelBlocks (tally n,(List.finRange d).map desc),tally j.val)).2,tally i.val) = _
  rw [blocks, Iter.search (nodes.map block) ([],[]) j.val (by simp [nodes]), List.getElem_map]
  change Iter.pick ([],[]) ((CRTTree.right nodes[j.val]).map desc,tally i.val) = _
  rw [Iter.search _ _ _ (by simp only [List.length_map]; exact i.isLt), List.getElem_map]

theorem targetWordRows_at (n : ℕ) (hn : n ≤ Nat.clog 2 d)
    (j : Fin (CRTTree.level n (List.finRange d)).length)
    (i : Fin (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val])).length)
    (y : CRT.Address a E) (inv : Bool) :
    let g := (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val]))[i.val]
    let bits := packedControl n (List.finRange d) (addressField a w pad y)
    let all := levelTables (levelQuery a w pad n y inv)
    targetWordRows (tagAt a w n j.val i.val inv,bits) =
      wordRows (tally (w g),((all[j.val]?.getD [])[i.val]?).getD []) := by
  dsimp only
  rw [targetWordRows, targetDescriptor_at a w n hn j i inv]
  exact congrArg (fun t => wordRows (tally _, t)) (selectTarget_eq _ _ _)

end CRTTable

end NearSquareRoot
end Computability
end OAI
