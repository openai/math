import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges
import OAI.Computability.BorderVNP.CellDirectoryRetained

/-! # Final placement of a retained sparse history

Absolute bit addresses translate together, and the stable box prefix selects
the same one-copy private factor list. This preserves the serialized record
length, public guard nodes, resolved sweep nodes and individual visit counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open scoped Classical

private theorem recordWordLength (r : Record) (off base : ℕ) :
    (Packet.record ((r.shift off).rebaseBox base)).length = (Packet.record r).length := by
  cases r <;> simp [Record.shift,Record.rebaseBox,Packet.record,Packet.port,Packet.fieldList,Packet.route,Function.comp_def]

private theorem guardShift (r : Record) (off : ℕ) : (r.shift off).guardMassBound = r.guardMassBound := by
  cases r <;> simp [Record.shift,Record.guardMassBound]

private theorem blocksShift (boxes : List (List Factor)) (rows : List Record) (off : ℕ) :
    Directory.resolvedRows boxes (rows.map (fun r => r.shift off)) =
      (Directory.resolvedRows boxes rows).map (fun b => {b with base := off+b.base}) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    cases r <;> simp [Directory.resolvedRows,Directory.blocks,Record.shift] at ih ⊢ <;> exact ih

/-- Word counts and all three costs of the actual final relocated records.
Each table lookup uses its true slot in the complete merged table. -/
theorem Site.placed_metrics (s : Site) (off base : ℕ) (boxes : List (List Factor))
    (valid : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length)
    (slot : ∀ i < s.boxes.length, boxes.getD (base+i) [] = s.boxes.getD i []) :
    let rows := s.placedRows off base
    let bs := Directory.resolvedRows boxes rows
    (Packet.fieldList Packet.record rows).length = (Packet.fieldList Packet.record s.rows).length ∧
      Directory.recordNodes rows = Directory.recordNodes s.rows ∧
      Directory.blockNodes bs = Directory.blockNodes s.directory.blocks ∧
      (bs.map fun b => b.copies*b.factors.length).sum = s.directory.visitCount := by
  intro rows bs
  let translated : Directory := ⟨s.boxes,s.rows.map (fun r => r.shift off),[]⟩
  have href : ∀ r ∈ translated.records, r.BoxRefFits s.boxes.length := by
    intro r hr
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    have ok := valid t ht
    cases t <;> exact ok
  have relocated := translated.blocks_rebaseBoxes_of_getD boxes base href slot
  have hb : bs = s.directory.blocks.map (fun b => {b with base := off+b.base}) := by
    have he : bs = (translated.rebaseBoxes boxes base).blocks := by
      change Directory.resolvedRows boxes (s.rows.map _) = Directory.resolvedRows boxes ((s.rows.map _).map _)
      rw [List.map_map]
      rfl
    rw [he,relocated]
    exact blocksShift s.boxes s.rows off
  refine ⟨?_,?_,?_,?_⟩
  · simp [rows,Site.placedRows,Packet.fieldList,List.length_flatMap,Function.comp_def,recordWordLength]
  · simp only [rows,Site.placedRows,Directory.recordNodes,List.length_map,List.map_map,Function.comp_def,
      Record.rebaseBox_guardMassBound,guardShift]
  · rw [hb]
    simp only [Directory.blockNodes,List.map_map,Function.comp_def]
  · rw [hb]
    simp only [Directory.visitCount,List.map_map,Function.comp_def]

end Packing.Inherited

end BorderVNP
end Computability
end OAI
