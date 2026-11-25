import OAI.Computability.BorderVNP.DiagonalNativeDispatchReceivingOwners
import OAI.Computability.BorderVNP.DiagonalFrozenIssuedReportReadback

/-! # The actual original and submitted rosters at one reached dispatch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyCellReports.ReportDirectory FiniteEvaluator FragmentRows TeamContraction
open BorderVNP.Cube Packing.RoutingOutputs

variable {R bundles ports bits w : ℕ} (a : SignedTaskArena.Layout) (u : Fin (R+1)) (address : ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs : Bank w} {memory : Memory w}
    (V : SignedPrep.Visits a.id pub mac regs memory)
    (host : Fin bundles → Fin a.cube.cells) (payload : Fin bundles → ReportBundle)
    (digits : ℕ → Fin a.p.report.gadgets → Fin a.p.report.countWidth → Bool)
    (coord : Fin (a.cube.n+1)) (description : ℕ)

set_option quotPrecheck false
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
local notation "original" => directoryCells directory rows layout₀ host payload middle digits
local notation "f" => FragmentRows.Layout.fromFrame frame (readings V.reports.val.2.2)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 6000 in
/-- An independently prepared original directory fixes the actual emitted owners.
Reading the chronological submitted rows at that emitter gives the exact
prepared inputs, allocations and supplemental streams needed by both the
native packet constructor and the prefix clock. -/
theorem Visits.reportsAtDispatch {prof initial written : ℕ → ℕ} {supplied : Fin a.cube.cells → ℕ}
    (entry : NativeEntry a.cube frame ctl coord R prof initial written)
    (frames : FrozenControlEntry a prog frame frame ctl (tbl).ends w supplied written owned)
    (room : a.OpenRoom frame (tbl).ends ctl (tbl).livePairs ports bundles (2^bits) w)
    (seed : PreparedReportInput pub control original a.after.reportCursor description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl coord) layout₀ original a.after.reportCursor)
    (canonical : List (ReportCell layout₀)) (same : SameReportCells original canonical)
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
  intro after base sup size selected byCell submitted
  have keep : CubeAllocation.HostRetention a.cube frame initial written owned :=
    ⟨frames.retained.primary,fun i hi lo₁ lo₂ => (frames.retained.lower i hi lo₁ lo₂).trans (entry.low i hi),
      frames.retained.tables⟩
  have who := V.receivingOwners_at_native_emission a host (ReportBundle.header ∘ payload) coord room frames.placement
    frames.ready seed alloc emitted ptr entry keep
  have spell : original=selected := a.localDirectory_sourceCells u coord host payload prof initial written owned entry
    keep frames.placement room after who digits
  have chosenSeed : PreparedReportInput pub control selected a.after.reportCursor description := spell ▸ seed
  have chosenAlloc : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl coord) layout₀ selected a.after.reportCursor :=
    spell ▸ alloc
  have sourceSame : SameReportCells selected canonical := spell ▸ same
  have chrono : submitted=selected := visitedReportRows_scan rows after byCell
  exact ⟨chosenSeed,chosenAlloc,same.source_seed seed,same.source_allocation alloc,rfl,
    chrono.symm ▸ (sourceSame.seedExtras_eq chosenAlloc).symm⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
