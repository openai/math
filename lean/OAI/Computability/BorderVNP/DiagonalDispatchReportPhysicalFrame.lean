import OAI.Computability.BorderVNP.DiagonalObservedDispatchReportRows

/-! # Transport of the issued report reads to the processor's frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyCellReports.ReportDirectory FiniteEvaluator FragmentRows TeamContraction
open BorderVNP.Cube Packing.RoutingOutputs Packing.BottomReports

variable {R sites ports w : ℕ} {t : SignedTaskArena.Layout} {u : Fin (R+1)}
    {address base frame : ℕ} {home : Fin sites → Fin t.cube.cells}
local notation3 (prettyPrint := false) "tbl" => bases address t.cube.cables t.cube.cells sites
local notation3 (prettyPrint := false) "ctl" => controlsBase address t.cube.cables t.cube.cells sites ports
local notation3 (prettyPrint := false) "chart" => reportLayout t.before t.after base ctl
  t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop

/-- The original report chart types the row list. The processor scans, writes
and publishes its directory at the frame recorded by the opening run. -/
theorem DispatchReportRows.atPhysicalFrame
    {pub : Arg → Word w} {control middle : Memory w} {payload : Fin sites → ReportBundle}
    {digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool}
    {axis : Fin (t.cube.n+1)} {description receiving : ℕ} {directory : List Packing.Directory.Row}
    {after : ℕ → ℕ} {canonical : List (ReportCell chart)}
    (recorded : DispatchReportRows t u (ports:=ports) address base home pub control payload digits axis
      description (readings (Packing.Directory.ISA.publish middle base receiving directory)) after canonical)
    (frameEq : frame=base) :
    let prior := readings (Packing.Directory.ISA.publish middle frame receiving directory)
    let rows := t.controlRows u.val frame (tbl).ends ctl (tbl).livePairs ports
    let bank := fun c => t.cube.cellBank+c*t.cube.cellStride
    let supply := fun c => prior ((tbl).ends+2*t.cube.cables+c)
    let width := fun c => prior ((tbl).livePairs+2*ports+c)
    let selected := sourceCells chart home payload u.val (rows.owner after) bank supply width digits
    let submitted := visitedReportRows rows after (sourceCell chart home payload bank supply width digits)
    PreparedReportInput pub control selected t.after.reportCursor description ∧
      ReportAllocation t.before t.after (t.cube.cellWriter frame ctl axis) chart selected t.after.reportCursor ∧
      PreparedReportInput pub control canonical t.after.reportCursor description ∧
      ReportAllocation t.before t.after (t.cube.cellWriter frame ctl axis) chart canonical t.after.reportCursor ∧
      t.before.tailWidths=(chart).tailWidths ∧
      seedExtras canonical t.after.reportCursor=seedExtras submitted t.after.reportCursor := by
  subst frame
  exact recorded

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
