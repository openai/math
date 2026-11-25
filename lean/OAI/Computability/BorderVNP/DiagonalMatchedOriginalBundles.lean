import OAI.Computability.BorderVNP.DiagonalReceivedOriginalVisits
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle
import OAI.Computability.BorderVNP.PackedBottomReportBundle

/-! # Original deliveries retained by a matching report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Packing.BottomReports DiagonalTallyCellReports DiagonalTallyAllocation

/-- Transfer the delivered original words and their room from the actual
sampled report to matching owner rows, including rows restored from the
packet's cell labels. -/
theorem SameReportCells.originalBundles {C sites w description : ℕ}
    {observed chosen : ReportLayout} {cells : List (ReportCell observed)} {reports : List (ReportCell chosen)}
    {host : Fin sites → Fin C} {header : Fin sites → BundleHeader}
    {payload factors : Fin sites → List CellSparse.Factor} {bits : Fin sites → ℕ → Bool} {ram : ℕ → ℕ}
    (same : SameReportCells cells reports)
    (received : ∀ j, (∃ c∈cells, (host j).val=c.number) →
      (physicalBundle (header j) (payload j) (factors j) (bits j)).delivered observed description ram ∧
      (physicalBundle (header j) (payload j) (factors j) (bits j)).SiteRoom observed w description) :
    ∀ j, (∃ c∈reports, c.number=(host j).val) →
      (physicalBundle (header j) (payload j) (factors j) (fun _ => false)).delivered chosen description ram ∧
      (physicalBundle (header j) (payload j) (factors j) (fun _ => false)).SiteRoom chosen w description := by
  obtain ⟨layout,rows⟩ := same
  subst chosen
  intro j visited
  have actual := (show SameReportCells cells reports from ⟨rfl,rows⟩).originalVisit _ visited
  obtain ⟨word,room⟩ := received j actual
  exact ⟨word,room.body,room.descriptionRoom,room.values,room.marked,room.padding,room.translated⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
