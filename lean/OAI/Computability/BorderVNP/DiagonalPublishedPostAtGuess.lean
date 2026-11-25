import OAI.Computability.BorderVNP.DiagonalPublishedPostWriter

/-! # The original published writer on the recovered local guess -/

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

variable {F origin}

set_option maxHeartbeats 1500000 in
/-- Recover the original writer at its physical pin spelling, then identify that spelling
with the local guess of the returning joint preparation. -/
def WriterPostRequest.PublishedWriter.fromPublicationAtGuess (request : WriterPostRequest a nodes active agent)
    {g : Fin (nodes agent).start.guessWidth → Bool}
    (guessEq : g = (active agent).1)
    {fields : Pins.ProcessorFields (request.startup.operands request.team request.slot request.packet).layout}
    {geometry returned : Memory w} {x : Exterior teams r₀ link → Bool} {headerBits : List Bool}
    {pinReg : Bank w} {pinMem : Memory w}
    (headerEq : headerBits=request.fields.bits) (exteriorEq : x=ext)
    (stateEq : (pinReg,pinMem)=((nodes agent).pins g).val.2)
    (geometryEq : geometry=returned)
    (resident : BootResidence (F:=fields) request.startup request.team request.slot request.packet request.copy request.advice
      (pubs agent) mac headerBits
      (processorMemory (G.processorFields agent col x (args agent).ibase (args agent).hbase (args agent).starbase) w)
      (regs agent) g returned)
    {directoryLayout : Packing.Directory.Layout} (same : F.dataDir=directoryLayout)
    {dimension ports : ℕ} {Port : Type} [Fintype Port] {portWidth : Port → ℕ} {N : Network dimension Port portWidth}
    {cell : N.Site → Fin a.cube.cells} {edgeID : N.Edge ↪ Fin a.cube.cables} {portID : Port ↪ Fin ports}
    {original : Fin directoryLayout.entries → N.Site} {live : (Fin directoryLayout.teams × Fin directoryLayout.sites) ↪ Port}
    {registers : Bank w} {pinCost profileCost : ℕ}
    (published : PublishedPin a directoryLayout N cell edgeID portID original live request.startup request.team request.slot request.packet
      request.destination request.gap request.copy headerBits fields (pubs agent) mac g
      pinReg pinMem registers geometry pinCost profileCost)
    (epoch : Returns epochPlacement (pubs agent) mac pinReg pinMem)
    (directory : Returns Packing.Directory.ISA.program (pubs agent) mac epoch.val.2.1 epoch.val.2.2)
    {before after : Bank w} {finalMemory : Memory w} {events : List (TeamRAM.Event w)}
    (writer : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (pubs agent) mac before directory.val.2.2
      events after finalMemory)
    (written : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner D F.group
      (G.pinLayout agent (F.inputBase agent) (F.columnBase agent) (F.referenceBase agent)) writer)
    (source : F.source origin agent=readings writer.sharedInput) : PublishedWriter F origin request := by
  subst g
  exact fromPublication request headerEq exteriorEq stateEq geometryEq resident same published
    epoch directory writer written source

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
