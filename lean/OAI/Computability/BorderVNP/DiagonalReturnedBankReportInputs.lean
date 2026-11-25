import OAI.Computability.BorderVNP.DiagonalPositiveCoreFrozenDirectory
import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.PackedBottomReportBundle

/-! # Native report preparation on the returned bundle bank and digit function -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator.SignedPrep TypedTaskBuilder DiagonalTallyAllocation
open Packing.BundleDirectory Packing.BottomReports

variable (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout) (layout : ReportLayout)
    (host : Fin d.bundles → Fin d.cells) (initial : ℕ → ℕ)

local notation3 (prettyPrint := false) "cells(" bundle "," digit ")" =>
  directoryCells d rows layout host bundle (grouped d host bundle initial) digit

/-- Stable grouping and the six native row fields are independent of the
sampled use bits and gadget digits, even on the original grouping memory. -/
theorem returnedBank_same_reports (before after : Fin d.bundles → ReportBundle)
    (first next : ℕ → Fin layout.gadgets → Fin layout.countWidth → Bool)
    (saved : ∀ j, SameBundleSource (before j) (after j)) :
    SameReportCells (cells(before,first)) (cells(after,next)) := by
  have headers : (fun j => (before j).header)=(fun j => (after j).header) := funext fun j => (saved j).header
  have held : grouped d host before initial=grouped d host after initial := by
    unfold grouped
    rw [headers]
  have columns : SameCellColumns rows rows (grouped d host before initial) (grouped d host after initial) := by
    rw [held]
    exact ⟨rfl,fun _ _ => Iff.rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  exact directoryCells_same_reports d d rows rows host host before after _ _ first next rfl columns rfl
    (fun _ => rfl) saved

/-- The original seed and report allocation also prepare the actual returned
bundle bank and proposed gadget values in the very same control memory. -/
theorem prepared_on_returned_bank {w : ℕ} {pub : Arg → Word w} {mem : Memory w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {cursor : ReportCursor}
    {description : ℕ} (before after : Fin d.bundles → ReportBundle)
    (first next : ℕ → Fin layout.gadgets → Fin layout.countWidth → Bool)
    (saved : ∀ j, SameBundleSource (before j) (after j))
    (prepared : PreparedReportInput pub mem (cells(before,first)) cursor description ∧
      ReportAllocation pre post banks layout (cells(before,first)) cursor) :
    PreparedReportInput pub mem (cells(after,next)) cursor description ∧
      ReportAllocation pre post banks layout (cells(after,next)) cursor := by
  have same := returnedBank_same_reports d rows layout host initial before after first next saved
  exact ⟨same.source_seed prepared.1,same.source_allocation prepared.2⟩

/-- Restoring another source bank in a physical bottom bundle preserves its
actual original header, opaque body and marked source positions. -/
theorem physicalBundle_same_source (hdr : BundleHeader) (body original : List CellSparse.Factor) (a b : ℕ → Bool) :
    SameBundleSource (physicalBundle hdr body original a) (physicalBundle hdr body original b) :=
  ⟨rfl,rfl,rfl⟩

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
