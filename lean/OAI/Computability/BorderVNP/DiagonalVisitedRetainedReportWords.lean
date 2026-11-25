import OAI.Computability.BorderVNP.DiagonalIssuedWriterRetention

/-! # Reading the selected writer's published words on its original report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP VPVNP.BurstRAM FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports
open BorderVNP.Cube BorderVNP.Cube.Physical Packing Evaluator.ScheduleClock

variable {R n w : ℕ} (task : SignedTaskArena.Layout)
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) {u : Fin (R+1)}
    (active : (U u).Prefix task.id)
local notation3 (prettyPrint := false) "V" => visits task.id U active
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "head" => (pub 0).val

/-- The report following the original return reads the initial directory from the
same placed memory using its actual public frame word. -/
theorem retainedReportWords
    {placed : Memory w} {first base : ℕ} {records : List Directory.Row}
    {written : ℕ → ℕ} (frame : first=head)
    (retained : CubeAllocation.HostRetention task.cube head
      (readings (Directory.ISA.publish placed first base records)) written (readings (V).owned.val.2.2))
    {J bankBits offsets ctl live ports : ℕ} (home : Fin J → Fin task.cube.cells)
    (headers : Fin J → BottomReports.BundleHeader)
    (ready : OpenSuffix.Ready (task.openInputs u.val head offsets ctl live ports J bankBits home headers)
      head (readings (V).owned.val.2.2) w)
    (placement : OpenSuffix.Placement (task.openInputs u.val head offsets ctl live ports J bankBits home headers)
      task.cube task.before head (readings (V).owned.val.2.2))
    {L : ReportLayout} {cells : List (ReportCell L)} {q : ReportCursor} {width : ℕ}
    (seed : PreparedReportInput pub (V).controls.val.2.2 cells q width)
    {banks : CellBanks.Layout} (allocation : ReportAllocation task.before task.after banks L cells q)
    (start : banks.bankStart=task.cube.cellBank) :
    SignedTaskArena.ReportWords task head (readings (Directory.ISA.publish placed head base records)) written
      (readings (V).reports.val.2.2) true := by
  subst first
  exact task.signed_report_words home headers (V).controls (V).reports seed retained ready placement allocation start

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
