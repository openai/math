import OAI.Computability.BorderVNP.DiagonalJointOwnedCableClock
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenLayouts

/-! # The complete argument charge on one actual supported team and pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows BorderVNP.Cube.TeamRowSources
open Scatter.Assignment FiniteEvaluator FiniteEvaluator.OpenSuffix Evaluator CellMacro.Generator CellDispatch DiagonalTallyCellReports
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {hist : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride hist pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {a : SignedTaskArena.Layout} {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) (p : PinStart.JointPrefix id U)
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {group : Fin a.cube.header.d → Fin (R+1)}
    {Site E I A P : Type} [Fintype A] [Fintype P]
    {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d} {recv : A → Fin a.cube.cells} {incoming : A → ℕ}
    {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {X width publicDepth chunkDepth originalTeams parameters exponent description fixedTicks : ℕ}
    {profile assigned : ℕ → ℕ}
    {offsets ctl live ports bundles b : ℕ} {bundleOwner : Fin bundles → Fin a.cube.cells}
    {bundleHeader : Fin bundles → Packing.BottomReports.BundleHeader}

set_option quotPrecheck false
set_option maxHeartbeats 2200000
set_option maxRecDepth 5000
local notation3 (prettyPrint := false) "owners" => greedyOwner R a.cube.b a.cube.s label recv incoming
local notation3 (prettyPrint := false) "family" => PinStart.ownedVisits (ar:=a.cube) U p

variable (u : Fin (R+1))
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "V" => PinStart.visits id U (p u)
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "ownedMem" => (V).owned.val.2.2
local notation3 (prettyPrint := false) "argMem" => (V).reports.val.2.2
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac (V).reports.val.2.1 argMem).symm (V).arguments
local notation3 (prettyPrint := false) "host" => HostScatter.Layout.fromFrame head (readings ownedMem)
local notation3 (prettyPrint := false) "ws" => LocalRow.weightLayout a.cube head decl.1.val
local notation3 (prettyPrint := false) "ts" => LocalRow.teamLayout a.cube R
local notation3 (prettyPrint := false) "H" => a.openInputs u.val head offsets ctl live ports bundles b bundleOwner bundleHeader

/-- A returning argument phase reads the original route's literal pair words,
the owned interval rows, and the same sparse tasks and report directory as
its local continuation. The cost uses the two true source packet depths and
the complete original-power rectangle. -/
theorem SharedWriters.arguments_on_joint_prefix (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count family)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) owners}
    (observed : ObservedOwned a.cube decl group family owners (f.receivedRows g group) q)
    (schedule : GroupWeights.ScheduleResult ws ts profile assigned)
    (image : GroupWeights.PhysicalImage ws profile a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv incoming)
    (pass : (TeamBudget.Layout.mk (R+1) X a.cube.teamTotals).Passes assigned)
    (copies : 1≤a.cube.K) (hw : 0<w) (descPositive : 1≤description)
    (fixedCost : (CubeConstants.install id).slots ≤ fixedTicks)
    (used : ℕ → ℕ) (padding : Padding.Returned a.cube decl.1 group u head w (readings ownedMem) used)
    (occupied : ∃ _ : (host).ScheduledCables (readings ownedMem) (a.cube.header.blocks*(a.cube.h*a.cube.b))
        decl.1 (fun z => (group z).val), (host).team=u.val ∧ (host).count=a.cube.cables)
    (ready : Ready H head (readings ownedMem) w) (fr : FragmentDirectoryInput pub argMem)
    (desc : LabelIndex.Layout) (after : ℕ → ℕ) (z axes : ℕ)
    (cableCount : desc.cableCount=a.cube.cables) (frCables : fr.layout.host.count=a.cube.cables)
    (frRows : fr.layout.count≤desc.deliveryCount) (frCells : fr.layout.cells≤desc.cells)
    (native : PinStart.SparseSource id U (p u)) {places : ℕ → CellPacket.Placed Site} {geom : ℕ → ℕ} {extra : ℕ → List CellSparse.Record}
    (production : ProducedRoster a (H).control (readings (parts).1.val.2.2) places geom extra native.source)
    (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned u.val description publicDepth chunkDepth
      originalTeams parameters exponent native.source fr.layout (readings argMem) (H).control (readings (parts).1.val.2.2))
    (cursor : ReportCursor) (seed : PreparedReportInput pub (V).controls.val.2.2 S.reportRows cursor description) :
    let input := PinStart.afterRoute id U (p u)
    traceCost input.val.1+privateDirectoryTicks pub input.val.2.2 ≤
      fixedTicks+
      argumentDirectory a.cube.cells bundles+32*descriptorTicks desc after z axes ws ts+
      (82*desc.cableCount+cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s width*(a.cube.alphabet^2+X+1))+
      cellWork w (2^publicDepth+2^chunkDepth) (originalTeams*(parameters*exponent)) X := by
  intro input
  obtain ⟨room,words,received⟩ := writer.received_on_joint_prefix U p symbols handoff u
  have legal : passesLengths a.cube.b a.cube.s q.1 decl := (passesLengths_iff ..).mpr observed.observed.1.symm
  have numbering : (fun z : Fin a.cube.header.d => assigned (a.cube.ownerBase+z.val))=fun z => (group z).val := by
    funext z
    exact (greedyOwner_stored schedule q.1 legal label recv incoming image z).trans (congrArg (fun h => (h z).val) observed.allocation)
  have tail := padding.tail
  have numeric : Padding.TailHeader decl.1 (fun z => (group z).val) (Function.Embedding.refl ℕ) u.val
      (Padding.Layout.fromFrame head (readings ownedMem)) (readings ownedMem) used a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s :=
    ⟨tail.alphabet,tail.banks,tail.site,tail.owners,tail.widths,tail.triples⟩
  obtain ⟨cables,team,physicalCount⟩ := occupied
  rw [←numbering] at words received numeric cables
  have positive : 0<a.cube.h*a.cube.b := Nat.pos_of_mul_pos_left room.payload
  have cost := PinStart.arguments_source_clock (width:=width) id U u (p u) native a copies room schedule image positive room.alphabet pass hw descPositive
    desc after z axes words received used numeric team cables (physicalCount.trans cableCount.symm).le H ready le_rfl
    fr (frCables.trans cableCount.symm).le frRows frCells production S cursor seed
  rw [show (H).bundles.bundles=bundles from rfl] at cost
  exact cost.trans (by gcongr)

end TeamContraction

end BorderVNP
end Computability
end OAI
