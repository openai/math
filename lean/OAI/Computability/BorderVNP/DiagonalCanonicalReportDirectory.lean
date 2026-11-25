import OAI.Computability.BorderVNP.DiagonalReportOrder
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory

/-! # Original report cells from the mathematical owner and width arrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open Packing.BundleDirectory RoutingISA TypedTaskBuilder

variable {J C : ℕ} (l : ReportLayout) (home : Fin J → Fin C) (payload : Fin J → ReportBundle)

/-- A cell's unfilled report holds its original sidecars, at the same offset
as in the native stable bundle grouping. -/
def sourceCell (bank supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (c : ℕ) : ReportCell l :=
  ⟨c,bank c,supply c,privateWidth c,«prefix» (groups home fun j => (payload j).header) c,
    (sourceRows home c).map payload,digits c⟩

/-- The source's per-team row list is determined even before a native
execution has been selected. It contains the actual owned cells in increasing
global order and uses the source bundle ordinal to break ties. -/
def sourceCells (team : ℕ) (who bank supply privateWidth : ℕ → ℕ)
    (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) : List (ReportCell l) :=
  ((List.range C).filter fun c => decide (who c=team)).map (sourceCell l home payload bank supply privateWidth digits)

variable (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (host : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)

/-- Reading the four physical columns suffices to identify every file of
actual native candidates with this independently indexed mathematical source. -/
theorem directoryCells_sourceCells (m : ℕ → ℕ) (size : rows.cells=d.cells)
    (who bank supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (read : ∀ c<d.cells, rows.owner m c=who c ∧ m (rows.banks+2*c+1)=bank c ∧
      m (rows.offsets+2*rows.cables+c)=supply c ∧ m (rows.live+2*rows.ports+c)=privateWidth c) :
    directoryCells d rows l host source m digits=sourceCells l host source rows.team who bank supply privateWidth digits := by
  let ids := List.ofFn fun i : Fin (rows.before m rows.cells) => globalCell rows.toLayout m i.val
  have enumerated : ids=(List.range d.cells).filter (fun c => decide (who c=rows.team)) := by
    refine (globalCell_prefix rows.toLayout m _ le_rfl).trans ?_
    rw [size]
    apply List.filter_congr
    intro c hc
    rw [(read c (List.mem_range.mp hc)).1]
  change (List.ofFn _) = _
  rw [show (List.ofFn fun i : Fin (rows.before m rows.cells) =>
        directoryCell d rows l host source m digits (globalCell rows.toLayout m i.val)) =
      ids.map (directoryCell d rows l host source m digits) by simp [ids, List.map_ofFn,Function.comp_def]]
  rw [enumerated]
  apply List.map_congr_left
  intro c hc
  obtain ⟨_,b,s,p⟩ := read c (List.mem_range.mp (List.mem_filter.mp hc).1)
  simp only [directoryCell,sourceCell,b,s,p]

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
