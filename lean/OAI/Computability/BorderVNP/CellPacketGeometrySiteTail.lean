import OAI.Computability.BorderVNP.CellPacketGeometrySiteOffsets

/-! # Public ordinals bounding the merged record and report fields of a cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
open private finRange_split from OAI.Computability.BorderVNP.CellPacketGeometrySiteOffsets

variable {C : ℕ} {S Orig : Type}

/-- Local offset of the record count after the two header words and all public boxes. -/
def Directory.tailStart (D : Directory S Orig C) (c : Fin C) : ℕ :=
  (select c (D.headers++D.boxRows)).length

/-- Length of the final public chunk (merged sparse records and report vectors). -/
def Directory.tailSize (D : Directory S Orig C) (c : Fin C) : ℕ :=
  (fieldList record (D.cellRecords c) ++ fieldList vector (D.reports c)).length

/-- The first word of the final public chunk is the cell's row count, and the
last is the final word of its nonempty report section. These are global ordinals
in different sections, but all intervening words of other cells are skipped by
the stable geometry sort. -/
def Directory.tailSpan (D : Directory S Orig C) (c : Fin C) :
    Span D.words c (D.tailStart c) (D.tailSize c) := by
  let counts := fun a : Fin C => [(D.cellRecords a).length]
  let reports := fun a : Fin C => fieldList vector (D.reports a)
  let preCount := D.headers ++ D.boxRows ++ siteRows id counts ((List.finRange C).take c.val)
  let postCount := siteRows id counts ((List.finRange C).drop (c.val+1)) ++ D.recordRows ++ D.reportRows
  let preReport := D.headers ++ D.boxRows ++ D.counts ++ D.recordRows ++
    siteRows id reports ((List.finRange C).take c.val)
  let postReport := siteRows id reports ((List.finRange C).drop (c.val+1))
  have hc : D.words = preCount++tag c (counts c)++postCount := by
    simp only [Directory.words,Directory.counts,finRange_split counts c,preCount,postCount,counts,List.append_assoc]
  have hr : D.words = preReport++tag c (reports c)++postReport := by
    simp only [Directory.words,Directory.reportRows,finRange_split reports c,preReport,postReport,reports,List.append_assoc]
  have cspan := span c preCount (counts c) postCount hc (by simp [counts])
  have rspan := span c preReport (reports c) postReport hr (by simp [reports,fieldList])
  have before : (select c preCount).length = D.tailStart c := by
    simp [preCount,Directory.tailStart,cell_prefix_empty]
  have records : select c D.recordRows = (D.cellRecords c).flatMap record := by
    simp [Directory.recordRows,Directory.cellRecords,select_sites,List.flatMap_assoc]
  have last : (select c preReport).length+(reports c).length-1 = D.tailStart c+D.tailSize c-1 := by
    simp only [preReport,select_append,cell_prefix_empty,List.append_nil,Directory.counts,select_cells,
      records,reports,Directory.tailStart,Directory.tailSize,List.length_append,List.length_nil,fieldList,List.length_cons]
    omega
  exact ⟨before ▸ cspan.first,last ▸ rspan.last⟩

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
