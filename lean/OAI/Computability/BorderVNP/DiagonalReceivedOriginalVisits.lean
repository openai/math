import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals

/-! # Original cell numbers are independent of every guessed report bit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open DiagonalTallyCellReports

/-- Recover the physical original-cell occurrence from its semantic row number. -/
theorem SameReportCells.originalVisit {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) (number : ℕ) (found : ∃ d∈ds, d.number=number) :
    ∃ c∈cs, number=c.number := by
  have stored : number∈ds.map ReportCell.number := List.mem_map.mpr found
  rw [←same.numbers] at stored
  obtain ⟨c,hc,equal⟩ := List.mem_map.mp stored
  exact ⟨c,hc,equal.symm⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
