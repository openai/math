import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalProducedRoster
import OAI.Computability.BorderVNP.RoutingISAScheduleClockInputVisits

/-! # Charging the actual signed arguments of a jointly reachable private call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM TeamContraction CompactMachine CellDispatch CellMacro.Generator BorderVNP.Cube
open Cube.Physical Cube.TeamRowClock Cube.TeamRowSources ScheduleClock DiagonalTallyCellReports
open BorderVNP.FiniteEvaluator.OpenSuffix

set_option maxHeartbeats 2300000
set_option maxRecDepth 4500

variable {teamsPred n w X width publicDepth chunkDepth originalTeams parameters exponent description : ℕ}
    {Site E I A P : Type} [Fintype A] [Fintype P] {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (U : Fin (teamsPred+1) → PinStart SparseExterior.driver n w) (u : Fin (teamsPred+1))
    (localRun : (U u).Prefix id)
    {orig assigned : ℕ → ℕ} {D : LengthDeclaration ar.n ar.header.d}
    {label : Fin ar.cells → Label (ar.n+1) ar.header.d} {recv : A → Fin ar.cells} {incoming : A → ℕ}
    (data : SparseSource id U localRun)
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "v" => visits id U localRun
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "weights" => LocalRow.weightLayout ar head D.1.val
local notation3 (prettyPrint := false) "teams" => LocalRow.teamLayout ar teamsPred
local notation3 (prettyPrint := false) "owner" => fun z : Fin ar.header.d => assigned (ar.ownerBase+z.val)
local notation3 (prettyPrint := false) "ownedMem" => (v).owned.val.2.2
local notation3 (prettyPrint := false) "reportMem" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "argumentMem" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "args" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 argumentMem).symm (v).arguments
local notation3 (prettyPrint := false) "host" => HostScatter.Layout.fromFrame head (readings ownedMem)
local notation3 (prettyPrint := false) "pad" => Padding.Layout.fromFrame head (readings ownedMem)

/-- Every returning input on this native prefix uses the very same compact
directory and physical sparse rows as its positive continuation. Charge the
installed constants, owned traversal, controls, report choices, task writes
and private probes; later rejection of a local cell is allowed. -/
theorem arguments_source_clock (arena : SignedTaskArena.Layout) (copies : 1 ≤ ar.K) (room : ar.ReplayRoom w head)
    (schedule : GroupWeights.ScheduleResult weights teams orig assigned)
    (image : GroupWeights.PhysicalImage weights orig ar.header.blocks ar.b ar.K ar.h D label recv incoming)
    (positive : 0<ar.h*ar.b) (alphabet : 0<ar.header.d)
    (pass : (TeamBudget.Layout.mk (teamsPred+1) X ar.teamTotals).Passes assigned)
    (hw : 0<w) (descPositive : 1 ≤ description)
    (desc : LabelIndex.Layout) (before : ℕ → ℕ) (z axes : ℕ)
    (words : ar.ScannerWords head u.val D.1.val owner (readings pub) (readings (v).constants.val.2.2) D.2)
    (received : LocalReceived ar head u.val D owner (v).constants.val.2.2)
    (used : ℕ → ℕ) (tail : Padding.TailHeader D.1 owner (Function.Embedding.refl ℕ) u.val pad (readings ownedMem) used
      ar.header.blocks ar.b ar.h ar.K ar.s)
    (teamId : (host).team=u.val) (cables : (host).ScheduledCables (readings ownedMem) (ar.header.blocks*(ar.h*ar.b)) D.1 owner)
    (hostCount : (host).count ≤ desc.cableCount)
    (L : Inputs) (ready : Ready L head (readings ownedMem) w) (bundleCount : L.bundles.cells ≤ ar.cells)
    (fr : FragmentDirectoryInput pub argumentMem) (frCables : fr.layout.host.count ≤ desc.cableCount)
    (frRows : fr.layout.count ≤ desc.deliveryCount) (frCells : fr.layout.cells ≤ desc.cells)
    {places : ℕ → CellPacket.Placed Site} {geom : ℕ → ℕ} {extra : ℕ → List CellSparse.Record}
    (roster : ProducedRoster arena L.control (readings (args).1.val.2.2) places geom extra data.source)
    (source : SparseReportSources Site E I P ar D label recv incoming assigned u.val description publicDepth chunkDepth
      originalTeams parameters exponent data.source fr.layout (readings argumentMem) L.control (readings (args).1.val.2.2))
    (q : ReportCursor) (seed : PreparedReportInput pub reportMem source.reportRows q description) :
    let input := afterRoute id U localRun
    traceCost input.val.1+privateDirectoryTicks pub input.val.2.2 ≤
      (CubeConstants.install id).slots+argumentDirectory ar.cells L.bundles.bundles+32*descriptorTicks desc before z axes weights teams+
        (82*desc.cableCount+cubeCoefficient ar.n ar.b ar.h ar.K ar.s width*(ar.alphabet^2+X+1))+
        cellWork w (2^publicDepth+2^chunkDepth) (originalTeams*(parameters*exponent)) X := by
  let x := afterRoute id U localRun
  have h := signedInputs_source_charge (Site:=Site) (E:=E) (I:=I) (P:=P) (team:=u) (width:=width) (p:=publicDepth) (d:=chunkDepth) (R:=originalTeams) (H:=parameters) (B:=exponent) id copies room schedule image
    positive alphabet pass hw descPositive desc before z axes x
  let split := SignedPrep.inputVisitsEquiv id pub mac (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s)
    (v).routing.val.2.1 (v).routing.val.2.2
  have same : split.symm x = ⟨(v).constants,(v).owned,(v).controls,(v).reports,(v).arguments⟩ :=
    split.symm_apply_apply _
  let cost := InputVisitCost (Site:=Site) (E:=E) (I:=I) (A:=A) (P:=P) (team:=u) (X:=X) (width:=width)
    (p:=publicDepth) (d:=chunkDepth) (R:=originalTeams) (H:=parameters) (B:=exponent) (description:=description)
    (label:=label) (recv:=recv) (incoming:=incoming) (assigned:=assigned) (D:=D) id desc before z axes x
  have observed := Eq.mp (congrArg cost same) h
  exact observed words received used tail teamId cables hostCount L ready bundleCount fr frCables frRows frCells
    roster.fields roster.room data.source source q seed

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
