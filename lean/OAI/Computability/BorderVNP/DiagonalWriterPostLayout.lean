import OAI.Computability.BorderVNP.DiagonalWriterPostRequest

/-! # Recover the native post-call charge across the installed layout equality -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

open BorderVNP.Cube.Physical BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacketGeometry CellDispatch Packing.BundleDirectory
open DiagonalTallyCellReports.ReportDirectory

open TeamContraction VPVNP BurstRAM TeamContraction.ProcessorSlots BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator

variable {teams n w r₀ clocks pinBits link inner : ℕ} {Edge : Type} {G : Wiring teams r₀ clocks pinBits link inner n Edge}
    {col : Fin pinBits → Bool} {ext : Exterior teams r₀ link → Bool}
    {pubs : Fin (teams+1) → Arg → Word w} {regs : Fin (teams+1) → Bank w} {args : Fin (teams+1) → UnitAddresses}
    (a : SignedTaskArena.Layout)
    (nodes : (i : Fin (teams+1)) → BootedPinStart SparseExterior.driver G pubs regs args col ext i)
    (active : PinStart.JointPrefix a.id (fun i => (nodes i).start)) (agent : Fin (teams+1))

local notation3 (prettyPrint := false) "pub" => ((fun i => (nodes i).start) agent).pub
local notation3 (prettyPrint := false) "frame" => (((fun i => (nodes i).start) agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n ((fun i => (nodes i).start) agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits a.id (fun i => (nodes i).start) (active agent)
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

open RoutingISA.Transmission TeamContraction.ProcessorSlots TeamContraction.JointHeader
open PackedHistoryCircuit RoutingISA.CompactMachine Diagonal.Layout Routing DiagonalTallyPacketEmit TeamScales BorderVNP.Cube.Tally
set_option maxHeartbeats 3300000
set_option maxRecDepth 7500


variable {a nodes active agent} (request : WriterPostRequest a nodes active agent)

/-- The recorded argument, private-call and final clocks of the original team. -/
def WriterPostRequest.Charge : Prop :=
  PinStart.ChargedPost a.id (fun i => (nodes i).start) request.budget a request.startup
    (6+3*request.gates+request.query) request.indexWidth (request.parameters+request.scalars) w
    ⌈publicWork (a.cube.n+1) request.alpha request.batch request.length (teams+1)⌉₊
    ⌈localWork (a.cube.n+1) request.logPower request.alpha request.exponent request.batch request.length (teams+1)⌉₊
    (cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s))
    (TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s) active agent

variable {b : SignedTaskArena.Layout} (layoutEq : a=b)
    (other : PinStart.JointPrefix b.id (fun i => (nodes i).start)) (visits : HEq active other)
    (directory : Packing.Directory.Layout) (directoryEq : request.directory=directory)
    (offsets ctl live ports : ℕ) (controlEq : request.control=ctl)

set_option maxHeartbeats 1500000 in
/-- Use the same startup, physical packet and numeric budget at an equal native
layout. The local routing arrays are those used by the receiving writer. -/
def WriterPostRequest.atLayout : WriterPostRequest b nodes other agent :=
  { directory := directory
    offsets := offsets
    control := ctl
    liveStart := live
    portCount := ports
    limit := request.limit
    budget := request.budget
    startup := request.startup
    reserve := request.reserve
    axes := request.axes
    groups := request.groups
    cap := request.cap
    query := request.query
    guesses := request.guesses
    gates := request.gates
    indexWidth := request.indexWidth
    parameters := request.parameters
    scalars := request.scalars
    batch := request.batch
    length := request.length
    logPower := request.logPower
    readerTicks := request.readerTicks
    alpha := request.alpha
    exponent := request.exponent
    wp := request.wp
    wd := request.wd
    privateSize := request.privateSize
    fields := by subst b; exact request.fields
    head := request.head
    feasible := by subst b; rw [← directoryEq,← controlEq]; exact request.feasible
    destination := request.destination
    readback := by subst b; obtain rfl := eq_of_heq visits; exact request.readback
    team := request.team
    slot := request.slot
    packet := request.packet
    copy := request.copy
    advice := request.advice
    layout := request.layout
    gap := request.gap
    base := request.base
    packetOrigin := request.packetOrigin
    cables := request.cables
    cells := request.cells
    rawBase := request.rawBase
    who := request.who
    subtotal := request.subtotal
    fresh := request.fresh
    areaSlots := request.areaSlots
    gateCount := request.gateCount
    outputs := request.outputs
    width := request.width
    off := request.off
    stripe := request.stripe
    literal := by subst b; rw [← directoryEq]; exact request.literal }

/-- Changing the native layout's name preserves the bits of the recorded header. -/
theorem WriterPostRequest.atLayout_header :
    (request.atLayout layoutEq other visits directory directoryEq offsets ctl live ports controlEq).fields.bits=request.fields.bits := by
  subst b
  obtain rfl := eq_of_heq visits
  rfl

set_option maxHeartbeats 1500000 in
/-- Transport the completed native charge back to the original issued prefix. -/
theorem WriterPostRequest.chargedOfLayout
    (done : (request.atLayout layoutEq other visits directory directoryEq offsets ctl live ports controlEq).Charge) : request.Charge := by
  subst b
  obtain rfl := eq_of_heq visits
  exact done

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
