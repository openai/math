import OAI.Computability.BorderVNP.DiagonalWriterPostAtOwner

/-! # The original published writer used by a native post-call request -/

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
open RoutingISA.Transmission TeamContraction.ProcessorSlots TeamContraction.JointHeader
open PackedHistoryCircuit RoutingISA.CompactMachine Diagonal.Layout Routing DiagonalTallyPacketEmit TeamScales BorderVNP.Cube.Tally
set_option maxHeartbeats 3300000
set_option maxRecDepth 7500

variable {a nodes active agent}
variable {D : LengthDeclaration a.cube.n a.cube.header.d} {wire : WireLayout (teams+1) r₀ link} {common : List Bool}
    {publicAt : HeaderExterior wire common → Fin (teams+1) → Arg → Word w}
    {macroAt : HeaderExterior wire common → Fin (teams+1) → TeamOpcode.Macros w 8}
    {regsAt : HeaderExterior wire common → Fin (teams+1) → Bank w}
    {memAt : HeaderExterior wire common → Fin (teams+1) → Memory w}
    (F : PreparationFrame G wire a.cube D common col publicAt macroAt regsAt memAt)
    (origin : HeaderExterior wire common)

/-- The boot and ordered writer selected by the registered source, on its original physical pin return. -/
structure WriterPostRequest.PublishedWriter (request : WriterPostRequest a nodes active agent) where
  /-- Resident processor fields in the allocated packet. -/
  fields : Pins.ProcessorFields (request.startup.operands request.team request.slot request.packet).layout
  /-- Memory at completion of the native geometry return. -/
  geometry : Memory w
  /-- Startup copied the registered header, processor pins and reference data into the published memory. -/
  resident : BootResidence (F:=fields) request.startup request.team request.slot request.packet request.copy request.advice
    (pubs agent) mac request.fields.bits
    (processorMemory (G.processorFields agent col ext (args agent).ibase (args agent).hbase (args agent).starbase) w)
    (regs agent) (active agent).1 geometry
  /-- Dimension of the selected physical network. -/
  dimension : ℕ
  /-- Capacity of its published port identifiers. -/
  portCount : ℕ
  /-- Physical ports of the routed network. -/
  Port : Type
  /-- Enumeration used by the signed directory. -/
  [finite : Fintype Port]
  /-- Number of bits stored on each network port. -/
  portWidth : Port → ℕ
  /-- Physical network being published. -/
  network : Network dimension Port portWidth
  /-- Map from physical sites to cube cells. -/
  cell : network.Site → Fin a.cube.cells
  /-- Cable number of every physical edge. -/
  edgeID : network.Edge ↪ Fin a.cube.cables
  /-- Published identifier of every port. -/
  portID : Port ↪ Fin portCount
  /-- Source site of each private directory entry. -/
  originalSite : Fin F.dataDir.entries → network.Site
  /-- Locations of the live ports in the network. -/
  nativePorts : (Fin F.dataDir.teams × Fin F.dataDir.sites) ↪ Port
  /-- Registers at the end of the profile code. -/
  profileRegisters : Bank w
  /-- Ticks already charged for pin processing. -/
  pinCost : ℕ
  /-- Ticks already charged for profile evaluation. -/
  profileCost : ℕ
  /-- The original pin and profile publish this very directory in the native geometry memory. -/
  published : PublishedPin a F.dataDir network cell edgeID portID originalSite nativePorts request.startup
    request.team request.slot request.packet request.destination request.gap request.copy request.fields.bits
    fields (pubs agent) mac (active agent).1 ((nodes agent).pins (active agent).1).val.2.1
    ((nodes agent).pins (active agent).1).val.2.2 profileRegisters geometry pinCost profileCost
  /-- Native epoch-placement return on the same original pin state. -/
  epoch : Returns epochPlacement (pubs agent) mac ((nodes agent).pins (active agent).1).val.2.1
    ((nodes agent).pins (active agent).1).val.2.2
  /-- Native directory publication after epoch placement. -/
  directory : Returns Packing.Directory.ISA.program (pubs agent) mac epoch.val.2.1 epoch.val.2.2
  /-- Registers before the ordered writer. -/
  writerStart : Bank w
  /-- Registers after the ordered writer. -/
  writerEnd : Bank w
  /-- Memory after the ordered writer. -/
  finalMemory : Memory w
  /-- Native event trace of the ordered writer. -/
  events : List (TeamRAM.Event w)
  /-- The original physical writer begins in the actual directory publication. -/
  writer : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (pubs agent) mac writerStart
    directory.val.2.2 events writerEnd finalMemory
  /-- The writer implements the selected frame's directory, allocation, owners and group scan. -/
  written : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner D F.group
      (G.pinLayout agent (F.inputBase agent) (F.columnBase agent) (F.referenceBase agent)) writer
  /-- The registered source is read from that writer's shared input. -/
  source : F.source origin agent=readings writer.sharedInput

variable {F origin}

set_option maxHeartbeats 1500000 in
/-- Recover the single typed writer from the original boot, pin, and directory
returns. The physical directory may be named using the calibrated layout. -/
def WriterPostRequest.PublishedWriter.fromPublication (request : WriterPostRequest a nodes active agent)
    {fields : Pins.ProcessorFields (request.startup.operands request.team request.slot request.packet).layout}
    {geometry returned : Memory w} {x : Exterior teams r₀ link → Bool} {headerBits : List Bool}
    {pinReg : Bank w} {pinMem : Memory w}
    (headerEq : headerBits=request.fields.bits) (exteriorEq : x=ext)
    (stateEq : (pinReg,pinMem)=((nodes agent).pins (active agent).1).val.2)
    (geometryEq : geometry=returned)
    (resident : BootResidence (F:=fields) request.startup request.team request.slot request.packet request.copy request.advice
      (pubs agent) mac headerBits
      (processorMemory (G.processorFields agent col x (args agent).ibase (args agent).hbase (args agent).starbase) w)
      (regs agent) (active agent).1 returned)
    {directoryLayout : Packing.Directory.Layout} (same : F.dataDir=directoryLayout)
    {dimension ports : ℕ} {Port : Type} [Fintype Port] {portWidth : Port → ℕ} {N : Network dimension Port portWidth}
    {cell : N.Site → Fin a.cube.cells} {edgeID : N.Edge ↪ Fin a.cube.cables} {portID : Port ↪ Fin ports}
    {original : Fin directoryLayout.entries → N.Site} {live : (Fin directoryLayout.teams × Fin directoryLayout.sites) ↪ Port}
    {registers : Bank w} {pinCost profileCost : ℕ}
    (published : PublishedPin a directoryLayout N cell edgeID portID original live request.startup request.team request.slot request.packet
      request.destination request.gap request.copy headerBits fields (pubs agent) mac (active agent).1
      pinReg pinMem registers geometry pinCost profileCost)
    (epoch : Returns epochPlacement (pubs agent) mac pinReg pinMem)
    (directory : Returns Packing.Directory.ISA.program (pubs agent) mac epoch.val.2.1 epoch.val.2.2)
    {before after : Bank w} {finalMemory : Memory w} {events : List (TeamRAM.Event w)}
    (writer : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (pubs agent) mac before directory.val.2.2
      events after finalMemory)
    (written : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner D F.group
      (G.pinLayout agent (F.inputBase agent) (F.columnBase agent) (F.referenceBase agent)) writer)
    (source : F.source origin agent=readings writer.sharedInput) : PublishedWriter F origin request := by
  have regEq := congrArg Prod.fst stateEq
  have memEq := congrArg Prod.snd stateEq
  dsimp only [Prod.fst, Prod.snd] at regEq memEq
  subst pinReg pinMem x headerBits returned directoryLayout
  exact {
    fields := fields
    geometry := geometry
    resident := resident
    dimension := dimension
    portCount := ports
    Port := Port
    finite := inferInstance
    portWidth := portWidth
    network := N
    cell := cell
    edgeID := edgeID
    portID := portID
    originalSite := original
    nativePorts := live
    profileRegisters := registers
    pinCost := pinCost
    profileCost := profileCost
    published := published
    epoch := epoch
    directory := directory
    writerStart := before
    writerEnd := after
    finalMemory := finalMemory
    events := events
    writer := writer
    written := written
    source := source }


end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
