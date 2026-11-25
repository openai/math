import OAI.Computability.BorderVNP.DiagonalSourceBootLookup
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom

/-! # The writer and boot evidence for a recovered ownership lookup -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace TeamContraction

open PackedHistoryCircuit
open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator
set_option maxHeartbeats 1500000
set_option maxRecDepth 7500

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (S : SourceReports sa.cube owners) (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)
    (B : F.Builders fixed sa.id owners) (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared sa.cube owners decl // S.pins v.val}) (reports : S.actual q.val.val)

local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "raw" => declaredWords sa.cube owners decl q.val
local notation3 (prettyPrint := false) "z" => F.replay fixed raw
local notation3 (prettyPrint := false) "physical" => (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
local notation3 (prettyPrint := false) "family" => ownedHistory sa.cube (pub z.1) (mac z.1)
  (fun u => ((B raw).constants u).val.2.1) (fun u => ((B raw).constants u).val.2.2) physical
local notation3 (prettyPrint := false) "visited" => fun u =>
  (visitsEquiv sa.id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)

local notation3 (prettyPrint := false) "data" => bankData q.val.val.2 sa.cube.header.packetBase sa.cube.singleBank
local notation3 (prettyPrint := false) "numbering" => Fin.valEmbedding ∘ owners q.val.val.1

/-- The global directory and the chronological epoch, publication and writer
histories whose source projection is used by this preparation frame. -/
structure PreparationFrame.LookupPublication where
  /-- Layout of the published demand directory. -/
  directory : Packing.Directory.Layout
  /-- Placement of private entrants in the directory. -/
  privatePlacement : ℕ → ℕ × ℕ
  /-- Placement of live entrants in the directory. -/
  livePlacement : ℕ → ℕ × ℕ
  /-- Processor receiving each directory entry. -/
  owner : ℕ → Fin (R+1)
  /-- Processor assigned to each shared symbol group. -/
  group : Fin sa.cube.header.d → Fin (R+1)
  /-- Base address of the reference frame. -/
  frame : ℕ
  /-- Proposed pin bits at each team. -/
  guess : Fin (R+1) → ℕ → Bool
  /-- Broadcast destination of each team. -/
  dst : Fin (R+1) → ℕ
  /-- Input-bank base of each team. -/
  ib : Fin (R+1) → ℕ
  /-- Saved-column base of each team. -/
  hb : Fin (R+1) → ℕ
  /-- Reference-bank base of each team. -/
  sb : Fin (R+1) → ℕ
  /-- Actual epoch-placement return for each exterior and team. -/
  epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u)
  /-- Directory publication starting from the corresponding epoch return. -/
  published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
    (epoch x u).val.2.1 (epoch x u).val.2.2
  /-- Registers at the writer's return. -/
  endReg : HeaderExterior L header → Fin (R+1) → Bank w
  /-- RAM at the writer's return. -/
  out : HeaderExterior L header → Fin (R+1) → Memory w
  /-- Chronological trace of the writers. -/
  events : HeaderExterior L header → Fin (R+1) → List (TeamRAM.Event w)
  /-- Writer histories starting from the published directories. -/
  history : ∀ x u, WriterHistory sa.cube.n (selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub x u) (mac x u)
    (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u)
  projection : PreparationFrame.WriterProjection G L sa.cube directory privatePlacement livePlacement owner decl
    group frame header pin guess dst ib hb sb pub mac reg mem epoch published endReg out events history F

/-- An actual startup and published directory on the chosen pin, including the
original signed packet and the geometry writer's return. -/
structure PreparationFrame.LookupStartup (u : Fin (R+1)) where
  /-- Returned reference writer whose input carries the lookup fields. -/
  publication : F.LookupPublication sa
  /-- Allocation of the startup banks. -/
  arena : StartupArena
  emitted : ReturnedWriters sa.cube publication.directory publication.privatePlacement publication.livePlacement
    publication.owner decl publication.group (G.pinLayout u (publication.ib u) (publication.hb u) (publication.sb u))
    (publication.history z.1 u)
  /-- Generator of the started machine's native library. -/
  generator : Fragment IO
  /-- Initial hardware registers of each team. -/
  hardware : Fin (R+1) → Bank w
  /-- Argument-bank addresses of each team. -/
  args : Fin (R+1) → UnitAddresses
  /-- Actual positive startup of the recovered team and exterior. -/
  boot : BootedPinStart generator G (pub z.1) hardware args pin z.1.val u
  /-- Pin choice that realizes the chosen start memory. -/
  sub : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool
  memAt : mem z.1 u=(boot.pins sub).val.2.2
  head : (pub z.1 u 0).val=arena.frame
  row : (args u).ibase=arena.ibase
  col : (args u).hbase=arena.hbase
  /-- Reference packet loaded by the original startup. -/
  packet : ReferencePacket w d
  loaded : BootHeaderState (G.processorFields u pin z.1.val (args u).ibase (args u).hbase (args u).starbase)
    (G.transferFrame u (args u).header (args u).dst) (args u).advice packet (pub z.1 u) (observed L z.1.val fixed)
    boot.out boot.memory
  /-- Literal words before installing the signed profile extension. -/
  old : Fin 81 → Word w
  /-- Number of geometry outputs. -/
  outputs : ℕ
  /-- Bound used in the geometry return. -/
  clock : ℕ
  /-- Beginning of the geometry's temporary allocation. -/
  fresh : ℕ
  /-- Base address at which the geometry outputs are written. -/
  dest : ℕ
  /-- Number of reserved profile bits. -/
  reserve : ℕ
  /-- Gate count of the installed geometry program. -/
  gates : ℕ
  /-- Word width of its output fields. -/
  fieldWidth : ℕ
  /-- Starting offset of the emitted geometry stripe. -/
  offset : ℕ
  /-- Width of the emitted geometry stripe. -/
  stride : ℕ
  literal : packet.extension=signedProfileExtension sa old publication.directory dest sa.cube.cables sa.cube.cells
    (rawAddress arena sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap) u.val w
    fresh reserve gates outputs fieldWidth offset stride
  /-- Integer values emitted by the geometry run. -/
  output : Fin outputs → ℕ
  /-- Event trace of that geometry run. -/
  trace : List (TeamRAM.Event w)
  /-- Registers returned by the geometry run. -/
  after : Bank w
  /-- Memory returned by the geometry run. -/
  geo : Memory w
  geometry : GeometryReturn (pub z.1 u) (mac z.1 u) (reg z.1 u) (mem z.1 u) fresh dest clock output trace after geo
  sourceRoom : arena.next ≤ fresh
  outputRoom : arena.next ≤ dest
  /-- Reserved cable capacity of the private layout. -/
  edgeCap : ℕ
  /-- Reserved cell capacity of the private layout. -/
  cellCap : ℕ
  /-- Padding of the private layout. -/
  gap : ℕ
  placement : (Packing.RoutingOutputs.privateLayout arena.frame dest edgeCap cellCap publication.directory.entries
    publication.directory.description gap).Image (readings geo) publication.directory.entries
    (readings (publication.epoch z.1 u).val.2.2)
  publishedAt : (publication.published z.1 u).val.2.2=Packing.Directory.ISA.publish (publication.epoch z.1 u).val.2.2
    arena.frame arena.next (publication.directory.directory publication.privatePlacement publication.livePlacement)
  room : sa.after.packed ≤ 2^w
  secondary : arena.next ≤ sa.cube.header.header
  capacity : (CubeVisits.teamList (data).axis sa.cube.header.blocks numbering u.val).length ≤ sa.p.report.vertices
  cubeWidth : argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth

/-- At one routed team, the startup snapshot and the genuine ownership
return. Both refer to the replay of the same declared shared words. -/
structure PreparationFrame.BootLookupAt (u : Fin (R+1)) extends F.LookupStartup sa fixed S q u where
  /-- Physical layout of the initial constant table. -/
  template : Frame
  /-- Number of rows in the indexed route table. -/
  slots : ℕ
  /-- Transmitting histories on the replayed exterior. -/
  teams : Fin (R+1) → TeamHistory w
  /-- Returned delivery on precisely those histories. -/
  delivery : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
    teams (fun v => G.pinLayout v (F.inputBase v) (F.columnBase v) (F.referenceBase v))
  writer : SharedWriters delivery F.rows (F.source z.1)
  rows : delivery.receivedRows F.rows F.group=(raw).val
  handoff : OwnedHandoff delivery F.rows (F.source z.1) sa.cube decl F.group template sa.id slots family
  groupMap : F.group=owners q.val.val.1

/-- Replay this particular boot and publication for any report guess and
demand; all lookup inputs come from the attained native ownership state. -/
theorem PreparationFrame.BootLookupAt.prepared {u : Fin (R+1)}
    (physicalInputs : F.BootLookupAt sa fixed S B q u) (demand : ℕ) :
    CubePacket.WordPrepared (gadgetLookup sa (pub full.1 u) numbering u.val demand data)
      sa.id (pub full.1 u) (visited u).owned.val.2.2 := by
  let h := physicalInputs
  let ctl := rawAddress h.arena sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap
  have fields := h.loaded.lookupFields sa h.old h.publication.directory h.dest sa.cube.cables sa.cube.cells ctl
    u.val w h.fresh h.reserve h.gates h.outputs h.fieldWidth h.offset h.stride h.literal
  exact F.sourceEquiv_boot_lookup sa fixed S B agree q reports h.publication.projection h.template h.slots h.delivery
    h.writer h.rows h.handoff h.groupMap u demand h.arena h.emitted h.hardware h.args h.boot h.sub h.memAt
    h.head h.row h.col h.old ctl u.val w fields h.geometry h.sourceRoom h.outputRoom h.placement h.publishedAt
    h.room h.secondary h.capacity h.cubeWidth

end TeamContraction

end BorderVNP
end Computability
end OAI
