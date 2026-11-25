import OAI.Computability.BorderVNP.DiagonalPublishedPostWriter
import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport
import OAI.Computability.BorderVNP.DiagonalWriterPostLayout

/-! # The charged post-call return on the physically acquired report -/

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
    {E I P A : Type} [Fintype P] [Fintype A] {J : ℕ}
    (d : EmittedReport a (fun i => (nodes i).start) agent (active agent) request.directory request.offsets
      request.control request.liveStart request.portCount E I P A request.wp request.wd request.privateSize J)
    {wire : WireLayout (teams+1) r₀ link} {common : List Bool}
    {publicAt : HeaderExterior wire common → Fin (teams+1) → Arg → Word w}
    {macroAt : HeaderExterior wire common → Fin (teams+1) → TeamOpcode.Macros w 8}
    {regsAt : HeaderExterior wire common → Fin (teams+1) → Bank w}
    {memAt : HeaderExterior wire common → Fin (teams+1) → Memory w}
    {F : PreparationFrame G wire a.cube d.declaration common col publicAt macroAt regsAt memAt}
    {origin : HeaderExterior wire common} {proto : DiagonalTallyPacketEmit.Frame} {amount : ℕ}
    {route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s)
      (greedyOwner teams a.cube.b a.cube.s d.label d.recv d.incoming)}

set_option quotPrecheck false
local notation3 (prettyPrint := false) "scan" => a.controlRows agent.val frame request.offsets request.control request.liveStart request.portCount
local notation3 (prettyPrint := false) "baseRows" =>
  sourceCells d.layout d.home d.payload agent.val ((scan).owner (readings d.emission.output)) d.external d.supply d.privateWidth d.digits

set_option maxHeartbeats 2200000 in
/-- Charge the native argument and private calls on this exact emitted report.
The protected banks, output registers, source writer and final clocks all
refer to the same recovered prefix. -/
theorem WriterPostRequest.finishEmitted
    (owned : F.ReturnedOwnershipAt a origin ext proto amount route (PinStart.ownedVisits (ar:=a.cube) (fun i => (nodes i).start) active))
    (window : d.Window request.limit request.budget)
    (layout : d.layout=reportLayout a.before a.after frame request.control a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop)
    (directory : F.dataDir=request.directory)
    (marked : ∀ x∈baseRows, ∀ y∈x.bundles, ∀ z∈y.positions, z.parameter<2^w ∧ z.place<w)
    (geometry : SparseGeometry a f request.offsets request.control)
    (controls : ∀ i : Fin 37, readings orig (request.control+i.val)=a.controls i.val)
    (source : WriterPostRequest.PublishedWriter F origin request) :
    PinStart.ChargedPost a.id (fun i => (nodes i).start) request.budget a request.startup
      (6+3*request.gates+request.query) request.indexWidth (request.parameters+request.scalars) w
      ⌈publicWork (a.cube.n+1) request.alpha request.batch request.length (teams+1)⌉₊
      ⌈localWork (a.cube.n+1) request.logPower request.alpha request.exponent request.batch request.length (teams+1)⌉₊
      (cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
        (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s))
      (TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s) active agent := by
  exact request.runAtOwner (label:=d.label) (recv:=d.recv) (incoming:=d.incoming) owned
    d.fit d.cells d.emission d.data d.patch d.row E I P inferInstance J d.layout d.home d.payload
    d.external d.supply d.privateWidth d.digits d.cursor d.seed d.issued window d.output_eq layout directory
    marked geometry controls source.fields source.geometry source.resident source.dimension source.portCount
    source.Port source.finite source.portWidth source.network source.cell source.edgeID source.portID source.originalSite
    source.nativePorts source.profileRegisters source.pinCost source.profileCost source.published source.epoch source.directory
    source.writerStart source.writerEnd source.finalMemory source.events source.writer source.written source.source

variable {decl₀ : LengthDeclaration a.cube.n a.cube.header.d}
    {labels : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {receiver : A → Fin a.cube.cells} {widths : A → ℕ}
    {F₀ : PreparationFrame G wire a.cube decl₀ common col publicAt macroAt regsAt memAt}
    {actualOwner : (Packet a.cube.n a.cube.header.d a.cube.header.blocks → Selector a.cube.n a.cube.K a.cube.h) →
      Fin a.cube.header.d → Fin (teams+1)}
    {route₀ : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) actualOwner}

set_option maxHeartbeats 1800000 in
/-- Use the coordinates recorded by the native report to apply the writer and
ownership of the registered frame to the very same charged emission. -/
theorem WriterPostRequest.finishRegisteredEmission
    (coordinates : (d.declaration,d.label,d.recv,d.incoming)=(decl₀,labels,receiver,widths))
    (ownerEq : actualOwner=greedyOwner teams a.cube.b a.cube.s labels receiver widths)
    (owned : F₀.ReturnedOwnershipAt a origin ext proto amount route₀
      (PinStart.ownedVisits (ar:=a.cube) (fun i => (nodes i).start) active))
    (window : d.Window request.limit request.budget)
    (layout : d.layout=reportLayout a.before a.after frame request.control a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop)
    (directory : F₀.dataDir=request.directory)
    (marked : ∀ x∈baseRows, ∀ y∈x.bundles, ∀ z∈y.positions, z.parameter<2^w ∧ z.place<w)
    (geometry : SparseGeometry a f request.offsets request.control)
    (controls : ∀ i : Fin 37, readings orig (request.control+i.val)=a.controls i.val)
    (source : WriterPostRequest.PublishedWriter F₀ origin request) : request.Charge := by
  obtain ⟨hd,h⟩ := Prod.mk.inj coordinates
  obtain ⟨hl,h⟩ := Prod.mk.inj h
  obtain ⟨hr,hw⟩ := Prod.mk.inj h
  subst actualOwner decl₀ labels receiver widths
  exact request.finishEmitted d owned window layout directory marked geometry controls source

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
