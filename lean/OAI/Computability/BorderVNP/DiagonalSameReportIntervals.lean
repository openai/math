import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsPlacement

/-! # Reindex the physical descriptor, bank and word bounds at the report installer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open DiagonalTallyCellReports
open private from_cells from_bundles from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

/-- Transfer the actual source's slot intervals and private-word bound to the
builder's inputs, even if a different tape is installed on its proposed rows. -/
theorem SameReportCells.physicalRoom {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) {description stride w : ℕ} (intervals : SiteIntervals ds description stride)
    (words : ∀ c∈ds, c.privateWires+c.supplied+c.tailWidth<2^w) :
    SiteIntervals cs description stride ∧ ∀ c∈cs,c.privateWires+c.supplied+c.tailWidth<2^w := by
  obtain ⟨layout,clear⟩ := same
  subst k
  change eraseReportBits cs=eraseReportBits ds at clear
  let rows : ReportAssignments ds := ⟨cs,clear⟩
  let tape := (reportAssignmentEquiv ds).symm rows
  have eq : cellsOfTape ds tape=cs := congrArg Subtype.val ((reportAssignmentEquiv ds).apply_symm_apply rows)
  rw [←eq]
  constructor
  · intro c hc b hb
    obtain ⟨row,hr,i,rfl⟩ := from_cells _ ds 0 hc
    obtain ⟨original,hm,j,rfl⟩ := from_bundles _ row.bundles _ hb
    have seen := intervals row hr original hm
    rw [ReportCell.withTape_tailWidth]
    exact seen
  · intro c hc
    obtain ⟨row,hr,i,rfl⟩ := from_cells _ ds 0 hc
    rw [ReportCell.withTape_tailWidth]
    exact words row hr

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
