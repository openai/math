import OAI.Computability.BorderVNP.DiagonalOriginalDispatchReportReadback
import OAI.Computability.BorderVNP.DiagonalReturnedBankReportInputs

/-! # The visited native report rows before and after the actual bank assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyCellReports.ReportDirectory FiniteEvaluator FragmentRows TeamContraction
open BorderVNP.Cube Packing.RoutingOutputs Packing.BottomReports

variable {R bundles ports bits w : ℕ} (a : SignedTaskArena.Layout) (u : Fin (R+1)) (address : ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs : Bank w} {memory : Memory w}
    (V : SignedPrep.Visits a.id pub mac regs memory)
    (host : Fin bundles → Fin a.cube.cells) (hdr : Fin bundles → BundleHeader)
    (body originalBody : Fin bundles → List CellSparse.Factor) (bank : Fin bundles → ℕ → Bool)
    (digits : ℕ → Fin a.p.report.gadgets → Fin a.p.report.countWidth → Bool)
    (coord : Fin (a.cube.n+1)) (description : ℕ)

set_option quotPrecheck false
local notation "payload" => fun j => physicalBundle (hdr j) (body j) (originalBody j) (bank j)
local notation "unfilled" => fun j => physicalBundle (hdr j) (body j) (originalBody j) (fun _ => false)
local notation "frame" => (pub 0).val
local notation "tbl" => bases address a.cube.cables a.cube.cells bundles
local notation "ctl" => controlsBase address a.cube.cables a.cube.cells bundles ports
local notation "directory" => a.bundleLayout frame ctl bundles
local notation "rows" => a.controlRows u.val frame (tbl).ends ctl (tbl).livePairs ports
local notation "layout₀" => reportLayout a.before a.after frame ctl a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop
local notation "prog" => a.openInputs u.val frame (tbl).ends ctl (tbl).livePairs ports bundles bits host (ReportBundle.header ∘ payload)
local notation "owned" => readings V.owned.val.2.2
local notation "control" => V.controls.val.2.2
local notation "middle" => grouped directory host payload (OpenSuffix.hostImage frame owned)
local notation "restored" => directoryCells directory rows layout₀ host payload middle digits
local notation "unfilledRows" => directoryCells directory rows layout₀ host unfilled
  (grouped directory host unfilled (OpenSuffix.hostImage frame owned)) (fun _ _ _ => false)
local notation "f" => FragmentRows.Layout.fromFrame frame (readings V.reports.val.2.2)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 6000 in
/-- On the original control-return memory, the independently prepared
unfilled directory supplies both seeds and both allocations for the returned
bank. The actual emitter and chronological submitted rows stay fixed. -/
theorem Visits.reportsAtReturnedBank {prof initial written : ℕ → ℕ} {supplied : Fin a.cube.cells → ℕ}
    (entry : NativeEntry a.cube frame ctl coord R prof initial written)
    (frames : FrozenControlEntry a prog frame frame ctl (tbl).ends w supplied written owned)
    (room : a.OpenRoom frame (tbl).ends ctl (tbl).livePairs ports bundles (2^bits) w)
    (prepared : PreparedReportInput pub control unfilledRows a.after.reportCursor description ∧
      ReportAllocation a.before a.after (a.cube.cellWriter frame ctl coord) layout₀ unfilledRows a.after.reportCursor)
    (canonical : List (ReportCell layout₀)) (same : SameReportCells unfilledRows canonical)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (emitted : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (frame+92)=ctl) :
    let after := readings emitted.output
    let base := fun c => a.cube.cellBank+c*a.cube.cellStride
    let sup := fun c => initial ((tbl).ends+2*a.cube.cables+c)
    let size := fun c => initial ((tbl).livePairs+2*ports+c)
    let selected := sourceCells layout₀ host payload u.val ((rows).owner after) base sup size digits
    let byCell := sourceCell layout₀ host payload base sup size digits
    let submitted := visitedReportRows rows after byCell
    PreparedReportInput pub control selected a.after.reportCursor description ∧
      ReportAllocation a.before a.after (a.cube.cellWriter frame ctl coord) layout₀ selected a.after.reportCursor ∧
      PreparedReportInput pub control canonical a.after.reportCursor description ∧
      ReportAllocation a.before a.after (a.cube.cellWriter frame ctl coord) layout₀ canonical a.after.reportCursor ∧
      a.before.tailWidths=(layout₀).tailWidths ∧
      seedExtras canonical a.after.reportCursor=seedExtras submitted a.after.reportCursor := by
  have saved (j : Fin bundles) : SameBundleSource (unfilled j) (payload j) :=
    physicalBundle_same_source (hdr j) (body j) (originalBody j) _ _
  have actual := returnedBank_same_reports directory rows layout₀ host (OpenSuffix.hostImage frame owned)
    unfilled payload (fun _ _ _ => false) digits saved
  have canonicalRows : SameReportCells restored canonical := by
    refine ⟨rfl,?_⟩
    exact (show eraseReportBits unfilledRows=eraseReportBits restored from actual.rows).symm.trans same.rows
  exact V.reportsAtDispatch a u address host payload digits coord description entry frames room
    (actual.source_seed prepared.1) (actual.source_allocation prepared.2) canonical canonicalRows emitted ptr

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
