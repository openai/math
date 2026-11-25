import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

/-! # One physical scanner allocation for all sampled source rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA DiagonalTallyAllocation
open private from_cells from_bundles from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

/-- A new sample of the same actual cell headers uses the same receiving
banks and the same owned-task output reservations, including for false counts. -/
theorem ReportAllocation.of_same {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {layout : ReportLayout} {cs ds : List (ReportCell layout)} {q : ReportCursor}
    (room : ReportAllocation pre post banks layout cs q) (same : eraseReportBits cs=eraseReportBits ds) :
    ReportAllocation pre post banks layout ds q := by
  let rows : ReportAssignments cs := ⟨ds,same.symm⟩
  let tape := (reportAssignmentEquiv cs).symm rows
  have eq : cellsOfTape cs tape=ds := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  rw [←eq]
  exact room.tape _ _

/-- Every power address read from a resampled report belongs to the original
source bundle. In particular its parameter ordinal and digit place are fixed. -/
theorem report_positions_of_same {layout : ReportLayout} {cs ds : List (ReportCell layout)}
    (same : eraseReportBits cs=eraseReportBits ds) {coordinate wordWidth : ℕ}
    (source : ∀ c∈cs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<coordinate ∧ p.place<wordWidth) :
    ∀ c∈ds, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<coordinate ∧ p.place<wordWidth := by
  let rows : ReportAssignments cs := ⟨ds,same.symm⟩
  let tape := (reportAssignmentEquiv cs).symm rows
  have eq : cellsOfTape cs tape=ds := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  rw [←eq]
  intro c hc b hb p hp
  obtain ⟨origin,original,pos,rfl⟩ := from_cells _ cs 0 hc
  obtain ⟨bundle,member,offset,rfl⟩ := from_bundles _ origin.bundles _ hb
  exact source origin original bundle member p hp

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
