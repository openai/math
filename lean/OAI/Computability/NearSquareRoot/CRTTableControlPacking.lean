import OAI.Computability.NearSquareRoot.CRTTableLevel

/-! # Packing a complete CRT control setting at one depth

Axis lists run from the least to most significant axis. A control header
concatenates the selected axis fields in the opposite order, keeping the
bits of each individual MSF field in their original order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

variable {α : Type*}

/-- The raw MSF field string on a list of axes in increasing significance. -/
def packFields (bits : α → List Bool) (xs : List α) : List Bool :=
  xs.reverse.flatMap bits

/-- The single raw control word provided to the full level's table solver. -/
def packedControl (n : ℕ) (axes : List α) (bits : α → List Bool) : List Bool :=
  packFields bits (CRTTree.controls n axes)

theorem packFields_length (bits : α → List Bool) (xs : List α) :
    (packFields bits xs).length = (xs.map (fun i => (bits i).length)).sum := by
  simp [packFields, List.length_flatMap, List.map_reverse]

theorem packedControl_length (n : ℕ) (axes : List α) (bits : α → List Bool) (desc : α → ControlAxis)
    (width : ∀ i ∈ axes, (bits i).length = (desc i).1.length) :
    (packedControl n axes bits).length =
      ((CRTTree.controls n axes).map (fun i => (desc i).1.length)).sum := by
  rw [packedControl, packFields_length]
  exact congrArg List.sum <| List.map_congr_left fun _ h =>
    width _ ((CRTTree.controls_sublist n axes).subset h)

/-- Every bit in the header belongs to a distinct position of the full-width
axis layout. This includes nodes with empty left children. -/
theorem packedControl_length_le (n : ℕ) (axes : List α) (bits : α → List Bool) (desc : α → ControlAxis)
    (width : ∀ i ∈ axes, (bits i).length = (desc i).1.length) {k : ℕ}
    (total : (axes.map (fun i => (desc i).1.length)).sum ≤ k) :
    (packedControl n axes bits).length ≤ k := by
  rw [packedControl_length n axes bits desc width]
  exact (((CRTTree.controls_sublist n axes).map _).sum_le_sum (by intros; omega)).trans total

private def segment (desc : α → ControlAxis) (bits : α → List Bool)
    (node : List α) : LevelBlock × List Bool :=
  (((CRTTree.left node).map desc,(CRTTree.right node).map desc),packFields bits (CRTTree.left node))

private theorem packedSegments (bits : α → List Bool) (desc : α → ControlAxis) (nodes : List (List α)) :
    (((nodes.map (segment desc bits)).reverse).map Prod.snd).flatten =
      packFields bits (nodes.flatMap CRTTree.left) := by
  induction nodes with
  | nil => simp [packFields]
  | cons node nodes ih =>
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.flatten_append,
      ih, List.flatMap_cons]
    simp [segment, packFields]

/-- The compiled level solver called with the packed fields returns one table
bundle per balanced-tree node, with its actual local left-child bits. -/
theorem levelTables_packed (n : ℕ) (axes : List α) (hn : n ≤ Nat.clog 2 axes.length)
    (desc : α → ControlAxis) (bits : α → List Bool) (inv : Bool)
    (width : ∀ i ∈ axes, (bits i).length = (desc i).1.length) :
    levelTables (inv,tally n,axes.map desc,packedControl n axes bits) =
      (CRTTree.level n axes).map (fun z =>
        nodeTables (inv,(CRTTree.left z).map desc,(CRTTree.right z).map desc,
          packFields bits (CRTTree.left z))) := by
  let segs := (CRTTree.level n axes).map (segment desc bits)
  have shape : segs.map Prod.fst =
      (CRTTree.level n (axes.map desc)).map (fun z => (CRTTree.left z,CRTTree.right z)) := by
    simp [segs, segment, CRTTree.level_map, List.map_map, Function.comp_def, CRTTree.left, CRTTree.right]
  have sizes : ∀ s ∈ segs, s.2.length = (leftRuler s.1).length := by
    intro s hs
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    simp only [segment, packFields_length, leftRuler_length, List.map_map, Function.comp_def]
    exact congrArg List.sum <| List.map_congr_left fun i h =>
      width i ((CRTTree.infix_of_mem_level hz).sublist.subset (List.mem_of_mem_take h))
  have packed : (segs.reverse.map Prod.snd).flatten = packedControl n axes bits :=
    packedSegments bits desc _
  rw [levelTables, levelBlocks_eq _ _ (by simpa using hn), ← shape, ← packed,
    batchTables_correct _ _ _ sizes]
  simp [segs, segment, List.map_map, Function.comp_def]

/-- The node lookup has no supplied segmentation or width certificate for a
node. Both are obtained from the original axis fields. -/
theorem levelTables_packed_getElem (n : ℕ) (axes : List α) (hn : n ≤ Nat.clog 2 axes.length)
    (desc : α → ControlAxis) (bits : α → List Bool) (inv : Bool)
    (width : ∀ i ∈ axes, (bits i).length = (desc i).1.length)
    (j : Fin (CRTTree.level n axes).length) :
    let node := (CRTTree.level n axes)[j.val]
    (levelTables (inv,tally n,axes.map desc,packedControl n axes bits))[j.val]'(by
      rw [levelTables_packed n axes hn desc bits inv width]
      simp) =
        nodeTables (inv,(CRTTree.left node).map desc,(CRTTree.right node).map desc,
          packFields bits (CRTTree.left node)) := by
  simp only [levelTables_packed n axes hn desc bits inv width, List.getElem_map]

end CRTTable

end NearSquareRoot
end Computability
end OAI
