import OAI.Computability.BorderVNP.DiagonalNativeReportBindings

/-! # The native private tape in a single returned directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open RoutingISA TypedTaskBuilder
open private tapeCells_get from OAI.Computability.BorderVNP.DiagonalNativeReportBindings

variable (dir : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout) (l : ReportLayout)
    (host : Fin dir.bundles → Fin dir.cells) (sources : Fin dir.bundles → ReportBundle)
    (loaded : ℕ → ℕ) (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)

local notation3 (prettyPrint := false) "cs" => directoryCells dir rows l host sources loaded digits

/-- Position of this global cell in the team's chronological choice tape. -/
noncomputable def localTapePosition (first c : ℕ) : ℕ :=
  first+(((cs).take (rows.before loaded c)).map ReportCell.tailWidth).sum

/-- The local scanner's actual grouped cell with its private selected bits. -/
noncomputable def localTapedCell (tape : ℕ → Bool) (first c : ℕ) : ReportCell l :=
  (directoryCell dir rows l host sources loaded digits c).withTape tape
    (localTapePosition dir rows l host sources loaded digits first c)

/-- The private row at the returned global ordinal uses exactly the bits
following all preceding local rows. No other team's ownership enters. -/
theorem localTapedCell_at (tape : ℕ → Bool) (first : ℕ) (i : Fin (rows.before loaded rows.cells)) :
    localTapedCell dir rows l host sources loaded digits tape first (globalCell rows.toLayout loaded i.val) =
      (tapeCells tape first cs)[i.val]'(by simpa only [tapeCells_length,directoryCells,List.length_ofFn] using i.isLt) := by
  let j : Fin (cs).length := ⟨i.val,by simpa only [directoryCells,List.length_ofFn] using i.isLt⟩
  have which := (global_spec rows.toLayout loaded i.isLt).2.2
  change rows.before loaded (globalCell rows.toLayout loaded i.val)=i.val at which
  rw [localTapedCell,localTapePosition,which,tapeCells_get tape first cs j]
  simp only [directoryCells,List.getElem_ofFn,j]

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
