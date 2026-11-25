import OAI.Computability.BorderVNP.DiagonalReturnedBankDispatch

/-! # The source chart and issued reports at the observed frame address -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyCellReports.ReportDirectory FiniteEvaluator FragmentRows TeamContraction
open BorderVNP.Cube Packing.RoutingOutputs Packing.BottomReports

variable {R sites ports w : ℕ} (t : SignedTaskArena.Layout) (u : Fin (R+1))
    (address head : ℕ) (home : Fin sites → Fin t.cube.cells)
local notation3 (prettyPrint := false) "tbl" => bases address t.cube.cables t.cube.cells sites
local notation3 (prettyPrint := false) "ctrl" => controlsBase address t.cube.cables t.cube.cells sites ports
local notation3 (prettyPrint := false) "chart" => reportLayout t.before t.after head ctrl
  t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "rows" => t.controlRows u.val head (tbl).ends ctrl (tbl).livePairs ports

/-- The issued row scan prepares its genuine assignment and its canonical
source in the original control memory. Its supplement agrees with the
submitted report traversal at the same physical emitter. -/
abbrev DispatchReportRows (pub : Arg → Word w) (control : Memory w) (payload : Fin sites → ReportBundle)
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
    (axis : Fin (t.cube.n+1)) (description : ℕ) (prior after : ℕ → ℕ) (canonical : List (ReportCell chart)) : Prop :=
  let base := fun c => t.cube.cellBank+c*t.cube.cellStride
  let sup := fun c => prior ((tbl).ends+2*t.cube.cables+c)
  let size := fun c => prior ((tbl).livePairs+2*ports+c)
  let selected := sourceCells chart home payload u.val ((rows).owner after) base sup size digits
  let submitted := visitedReportRows rows after (sourceCell chart home payload base sup size digits)
  PreparedReportInput pub control selected t.after.reportCursor description ∧
    ReportAllocation t.before t.after (t.cube.cellWriter head ctrl axis) chart selected t.after.reportCursor ∧
    PreparedReportInput pub control canonical t.after.reportCursor description ∧
    ReportAllocation t.before t.after (t.cube.cellWriter head ctrl axis) chart canonical t.after.reportCursor ∧
    t.before.tailWidths=(chart).tailWidths ∧ seedExtras canonical t.after.reportCursor=seedExtras submitted t.after.reportCursor

variable {bound : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs : Bank w} {memory : Memory w}
    (V : Visits t.id pub mac regs memory) (hdr : Fin sites → BundleHeader)
    (body original : Fin sites → List CellSparse.Factor) (bank : Fin sites → ℕ → Bool)
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
    (axis : Fin (t.cube.n+1)) (description : ℕ)

local notation3 (prettyPrint := false) "payload" => fun j => physicalBundle (hdr j) (body j) (original j) (bank j)
local notation3 (prettyPrint := false) "empty" => fun j => physicalBundle (hdr j) (body j) (original j) (fun _ => false)
local notation3 (prettyPrint := false) "prog" =>
  t.openInputs u.val head (tbl).ends ctrl (tbl).livePairs ports sites bound home hdr
local notation3 (prettyPrint := false) "group" => t.bundleLayout head ctrl sites
local notation3 (prettyPrint := false) "owned" => readings V.owned.val.2.2
local notation3 (prettyPrint := false) "originals" => directoryCells group rows chart home empty
  (grouped group home empty (OpenSuffix.hostImage head owned)) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "memory₀" => V.reports.val.2.2
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame (pub 0).val (readings memory₀)

set_option maxHeartbeats 1800000 in
/-- The true control entry identifies its original frame address with the
local program frame. This reindexes the entire six-part dispatch readback
together with the original source directory. -/
theorem Visits.reportsAtObservedFrame {prof initial written : ℕ → ℕ} {supplied : Fin t.cube.cells → ℕ}
    (entry : NativeEntry t.cube head ctrl axis R prof initial written)
    (opened : FrozenControlEntry t prog head (pub 0).val ctrl (tbl).ends w supplied written owned)
    (room : t.OpenRoom head (tbl).ends ctrl (tbl).livePairs ports sites (2^bound) w)
    (canonical : List (ReportCell chart))
    (prepared : (PreparedReportInput pub V.controls.val.2.2 originals t.after.reportCursor description ∧
      ReportAllocation t.before t.after (t.cube.cellWriter head ctrl axis) chart originals t.after.reportCursor) ∧
      SameReportCells originals canonical)
    {fit : (f).Fits w (readings memory₀)} {cells : t.fragments.cells=(f).cells}
    (emitted : SparseEmission t f memory₀ fit cells) (pointer : readings memory₀ ((pub 0).val+92)=ctrl) :
    DispatchReportRows t u (ports:=ports) address head home pub V.controls.val.2.2 payload digits axis description
      initial (readings emitted.output) canonical := by
  have atFrame := opened.frame
  subst head
  exact V.reportsAtReturnedBank t u address home hdr body original bank digits axis description entry opened room
    prepared.1 canonical prepared.2 emitted pointer

local notation3 (prettyPrint := false) "resolvedRows" => directoryCells group rows chart home payload
  (grouped group home payload (OpenSuffix.hostImage head owned)) digits

set_option maxHeartbeats 1800000 in
/-- The pointwise report tests on a selected lookup already prepare its own
bundle bank. The observed frame transports that very list to the emitter. -/
theorem Visits.reportsAtMatchingFrame {prof initial written : ℕ → ℕ} {supplied : Fin t.cube.cells → ℕ}
    (entry : NativeEntry t.cube head ctrl axis R prof initial written)
    (opened : FrozenControlEntry t prog head (pub 0).val ctrl (tbl).ends w supplied written owned)
    (room : t.OpenRoom head (tbl).ends ctrl (tbl).livePairs ports sites (2^bound) w)
    (canonical : List (ReportCell chart))
    (prepared : (PreparedReportInput pub V.controls.val.2.2 resolvedRows t.after.reportCursor description ∧
      ReportAllocation t.before t.after (t.cube.cellWriter head ctrl axis) chart resolvedRows t.after.reportCursor) ∧
      SameReportCells resolvedRows canonical)
    {fit : (f).Fits w (readings memory₀)} {cells : t.fragments.cells=(f).cells}
    (emitted : SparseEmission t f memory₀ fit cells) (pointer : readings memory₀ ((pub 0).val+92)=ctrl) :
    DispatchReportRows t u (ports:=ports) address head home pub V.controls.val.2.2 payload digits axis description
      initial (readings emitted.output) canonical := by
  have atFrame := opened.frame
  subst head
  exact V.reportsAtDispatch t u address home payload digits axis description entry opened room
    prepared.1.1 prepared.1.2 canonical prepared.2 emitted pointer

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
