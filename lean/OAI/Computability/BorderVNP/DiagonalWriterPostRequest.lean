import OAI.Computability.BorderVNP.DiagonalDeployedIssuedPrefixPost

/-! # Fixed physical operands for each issued post-call proof -/

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


/-- Fixed operands of the native post-call proof at one original prefix. -/
structure WriterPostRequest where
  /-- Directory of the published private and live tasks. -/
  directory : Packing.Directory.Layout
  /-- Base address of the routing end offsets. -/
  offsets : ℕ
  /-- First word of the 37 routing controls. -/
  control : ℕ
  /-- Address of the live-pair directory. -/
  liveStart : ℕ
  /-- Number of live ports represented by the directory. -/
  portCount : ℕ
  /-- Exterior budget stored in the packet. -/
  limit : ℕ
  /-- Time reserved for the argument preparation and private calls. -/
  budget : ℕ
  /-- Physical boot arena on this prefix. -/
  startup : StartupArena
  /-- Bit capacity of the compiled profile. -/
  reserve : ℕ
  /-- Number of cube axis labels encoded in the positive header. -/
  axes : ℕ
  /-- Number of symbols in the outer alphabet. -/
  groups : ℕ
  /-- Bound on the declaration slots of the positive header. -/
  cap : ℕ
  /-- Number of physical reader input bits. -/
  query : ℕ
  /-- Number of available reader guesses. -/
  guesses : ℕ
  /-- Number of gates in the chosen reader. -/
  gates : ℕ
  /-- Number of bits encoding the original pin index. -/
  indexWidth : ℕ
  /-- Number of parameters of the paired table. -/
  parameters : ℕ
  /-- Number of scalar identifiers in the coefficient reader. -/
  scalars : ℕ
  /-- Selected batch size. -/
  batch : ℕ
  /-- Length at which the schedule is evaluated. -/
  length : ℕ
  /-- Logarithmic exponent of the local-work bound. -/
  logPower : ℕ
  /-- Charge of the chosen reader program. -/
  readerTicks : ℕ
  /-- Exponent of the public-work schedule. -/
  alpha : ℝ
  /-- Exterior exponent used in the local-work bound. -/
  exponent : ℝ
  /-- First sort depth of the installed geometry directory. -/
  wp : ℕ
  /-- Second sort depth of the installed geometry directory. -/
  wd : ℕ
  /-- Number of digits allocated for a local packet count. -/
  privateSize : ℕ
  /-- Positive fields decoded from this prefix. -/
  fields : PositiveFields reserve axes groups cap a.cube.teams a.dim w
  /-- The startup frame is the one given by the actual team public bank. -/
  head : frame=startup.frame
  /-- The installed widths and windows fit the task and support both final charges. -/
  feasible : a.DeployedFeasiblePost startup directory control reserve axes groups cap w query guesses gates indexWidth
    batch wp wd privateSize limit ⌈publicWork (a.cube.n+1) alpha batch length (teams+1)⌉₊
    ⌈localWork (a.cube.n+1) logPower alpha exponent batch length (teams+1)⌉₊ readerTicks (teams+1) parameters scalars
  /-- Start of the routing output. -/
  destination : ℕ
  /-- The writer restores the protected banks on this actual prefix. -/
  readback : BootedPinStart.PublishedSourceReadback a nodes active agent startup fields destination
    (6+3*gates+query) indexWidth
  /-- Team slot in the startup arena. -/
  team : Fin startup.teams
  /-- Offset used to locate the advice in the team public bank. -/
  slot : ℕ
  /-- Reference packet actually installed at this team. -/
  packet : ReferencePacket w pinBits
  /-- Frame used to broadcast the reference data. -/
  copy : BroadcastFrame
  /-- Layout used to read this team’s advice. -/
  advice : AdviceLayout
  /-- The reference packet uses the pin layout of the chosen wiring. -/
  layout : (startup.operands team slot packet).layout = G.pinLayout agent (args agent).ibase (args agent).hbase (args agent).starbase
  /-- Spacing reserved between private demands. -/
  gap : ℕ
  /-- Executable budget words preceding the signed profile. -/
  base : Fin 81 → Word w
  /-- Origin stored in the signed packet. -/
  packetOrigin : ℕ
  /-- Number of physical cable positions in the extension. -/
  cables : ℕ
  /-- Number of physical cells in the extension. -/
  cells : ℕ
  /-- Address of the raw tally. -/
  rawBase : ℕ
  /-- This team’s physical ordinal. -/
  who : ℕ
  /-- Width of a subtotal word. -/
  subtotal : ℕ
  /-- Beginning of the native allocation area. -/
  fresh : ℕ
  /-- Number of available allocation slots. -/
  areaSlots : ℕ
  /-- Size of the installed geometry gate table. -/
  gateCount : ℕ
  /-- Number of output words in the located geometry table. -/
  outputs : ℕ
  /-- Physical word width recorded in the extension. -/
  width : ℕ
  /-- Offset used to stripe the literal data. -/
  off : ℕ
  /-- Width of an installed literal stripe. -/
  stripe : ℕ
  /-- The installed packet extension is the signed geometry and budget literal. -/
  literal : packet.extension=signedProfileExtension a base directory packetOrigin cables cells rawBase who subtotal
    fresh areaSlots gateCount outputs width off stripe

variable {a nodes active agent}
set_option quotPrecheck false
local notation3 (prettyPrint := false) "writer(" p ")" =>
  @obtained_writer_post (a:=a) (nodes:=nodes) (active:=active) (agent:=agent)
    (ext:=ext) (fields:=(p).fields) (headEq:=(p).head) (read:=(p).readback) (demand:=0)
    (sf:=(p).feasible) (index₀:=(p).team) (slot:=(p).slot) (reference:=(p).packet) (copy:=(p).copy)
    (advice:=(p).advice) (copyHeader:=(p).fields.bits) (sameLayout:=(p).layout) (literal:=(p).literal)
    (dir:=(p).directory) (offsets:=(p).offsets) (ctl:=(p).control) (live:=(p).liveStart)
    (ports:=(p).portCount) (X:=(p).limit) (budget:=(p).budget) (startup:=(p).startup)
    (reserve:=(p).reserve) (axes:=(p).axes) (groups:=(p).groups) (cap:=(p).cap) (query:=(p).query)
    (guesses:=(p).guesses) (gates:=(p).gates) (indexWidth:=(p).indexWidth) (parameters:=(p).parameters) (scalars:=(p).scalars)
    (batch:=(p).batch) (length:=(p).length) (logPower:=(p).logPower) (readerTicks:=(p).readerTicks) (α:=(p).alpha) (ξ:=(p).exponent)
    (wp:=(p).wp) (wd:=(p).wd) (B:=(p).privateSize)
    (dest:=(p).destination) (gap:=(p).gap) (base:=(p).base) (packetOrigin:=(p).packetOrigin) (cables:=(p).cables)
    (cellCount:=(p).cells) (rawBase:=(p).rawBase) (who:=(p).who) (subtotal:=(p).subtotal) (fresh:=(p).fresh)
    (areaSlots:=(p).areaSlots) (gateCount:=(p).gateCount) (outputs:=(p).outputs) (width:=(p).width)
    (off:=(p).off) (ell:=(p).stripe)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
/-- The remaining evidence is the native writer, report and call data on this same prefix. -/
def WriterPostRequest.Port (q : WriterPostRequest a nodes active agent) : Prop := type_of% writer(q)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
/-- Eliminate the native residual evidence once on the abstract prefix. -/
theorem WriterPostRequest.run (q : WriterPostRequest a nodes active agent) : q.Port := writer(q)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
