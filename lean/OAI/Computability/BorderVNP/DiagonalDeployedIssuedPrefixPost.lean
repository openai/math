import OAI.Computability.BorderVNP.DiagonalChargedPostProjection
import OAI.Computability.BorderVNP.DiagonalIssuedWriterRetention
import OAI.Computability.BorderVNP.DiagonalIssuedPrefixPhysicalPost
import OAI.Computability.BorderVNP.DiagonalDeployedPublishedSourceBanks
import OAI.Computability.BorderVNP.DiagonalPublishedPostInputs

/-! # The native frozen publication and its original tuple's pre-call and post-call clocks -/

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

variable {fit : (FragmentRows.Layout.fromFrame (((fun i => (nodes i).start) agent).pub 0).val (readings (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2)).Fits w
      (readings (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame (((fun i => (nodes i).start) agent).pub 0).val (readings (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame (((fun i => (nodes i).start) agent).pub 0).val (readings (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2))
      (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val (((fun i => (nodes i).start) agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val (((fun i => (nodes i).start) agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame (((fun i => (nodes i).start) agent).pub 0).val (readings (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2))
        (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).reports.val.2.2 data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=agent.val) («frame»:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

variable {E I P A : Type} [Fintype P] [Fintype A] {wp wd copies H B : ℕ}
    (D : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
    {J : ℕ} (L : ReportLayout) (home : Fin J → Fin a.cube.cells) (payload : Fin J → ReportBundle)
    (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    {q : ReportCursor}
local notation "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation "baseReports" => sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits
variable (seed : PreparedReportInput (((fun i => (nodes i).start) agent).pub) (PinStart.visits a.id (fun i => (nodes i).start) (active agent)).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val (((fun i => (nodes i).start) agent).pub 0).val offsets ctl live ports).owner
      (readings e.output)) eb supply privateWidth digits) q dir.description)
local notation "tape" => seed.returnedTape (v).reports
local notation "position" => returnedTapePosition R raw baseReports
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "actualReports" => ((assignedReportReturnEquiv seed mac (v).controls.val.2.1).symm (v).reports).val
local notation "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming

open RoutingISA.Transmission TeamContraction.ProcessorSlots TeamContraction.JointHeader
open PackedHistoryCircuit RoutingISA.CompactMachine Diagonal.Layout Routing DiagonalTallyPacketEmit TeamScales BorderVNP.Cube.Tally
set_option maxHeartbeats 3300000
set_option maxRecDepth 7500

variable {wire : WireLayout (teams+1) r₀ link} {common : List Bool}
  {publicAt : HeaderExterior wire common → Fin (teams+1) → Arg → Word w}
  {macroAt : HeaderExterior wire common → Fin (teams+1) → TeamOpcode.Macros w 8}
  {regsAt : HeaderExterior wire common → Fin (teams+1) → Bank w}
  {memAt : HeaderExterior wire common → Fin (teams+1) → Memory w}
  (F : PreparationFrame G wire a.cube D common col publicAt macroAt regsAt memAt)
  (origin : HeaderExterior wire common)
  {proto : DiagonalTallyPacketEmit.Frame} {amount : ℕ}
  (route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) (greedyOwner teams a.cube.b a.cube.s label recv incoming))
  (owned : F.ReturnedOwnershipAt a origin ext proto amount route (PinStart.ownedVisits (ar:=a.cube) (fun i => (nodes i).start) active))

include owned in
/-- The submitted argument and the native post-call executions share the same
original grouped source, in the order in which the local scanner actually
issued it. No check of a proposed report or subtotal is needed before its
post-call clock is charged. -/
theorem obtained_published_post
    {X budget : ℕ} (issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd)
      (copies:=a.cube.teams) (H:=a.p.parameters) (B:=B) a a.id (fun i => (nodes i).start) (active agent) e dir patch row D label recv incoming
      L home payload eb supply privateWidth digits seed)
    (published : PinStart.PublishedArgumentWindow a a.id (fun i => (nodes i).start) (active agent) D label recv incoming X dir.description wp wd
      a.cube.teams a.p.parameters B f R raw budget)
    (banked : e.output=(stages).1.val.2.2)
    (physicalLayout : L=reportLayout a.before a.after frame ctl a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop)
    (directory : F.dataDir=dir)
    (marked : ∀ x∈baseReports, ∀ y∈x.bundles, ∀ z∈y.positions, z.parameter<2^w ∧ z.place<w)
    (reported : IssuedReportFrame a pub (v).reports.val.2.2 offsets ctl (F.dataDir.directory F.privatePlacement F.livePlacement).length)
    {reserve axes groups cap query guesses gates indexWidth parameters scalars : ℕ} (startup : StartupArena)
    (fields : PositiveFields reserve axes groups cap a.cube.teams a.dim w)
    (headEq : frame=startup.frame) (demand : ℕ)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (sf : a.DeployedFeasiblePost startup dir ctl reserve axes groups cap w query guesses gates indexWidth batch wp wd B X
      ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊ readerTicks (teams+1) parameters scalars)
    (dest : ℕ) (read : BootedPinStart.PublishedSourceReadback a nodes active agent startup fields dest
      (6+3*gates+query) indexWidth)
    (index₀ : Fin startup.teams) (slot : ℕ) (reference : ReferencePacket w pinBits) (copy : BroadcastFrame)
    (advice : AdviceLayout) (residentFields : Pins.ProcessorFields (startup.operands index₀ slot reference).layout)
    (copyHeader : List Bool)
    (sameLayout : (startup.operands index₀ slot reference).layout =
      G.pinLayout agent (args agent).ibase (args agent).hbase (args agent).starbase)
    {geo : Memory w}
    (resident : BootResidence (F:=residentFields) startup index₀ slot reference copy advice (pubs agent)
      (install SparseExterior.driver n (nodes agent).start.routines)
      copyHeader (processorMemory (G.processorFields agent col ext (args agent).ibase (args agent).hbase (args agent).starbase) w)
      (regs agent) (active agent).1 geo)
    (gap : ℕ)
    {netDim portCount : ℕ} {Port : Type} [Fintype Port] {portWidth : Port → ℕ} (network : Network netDim Port portWidth)
    (cell : network.Site → Fin a.cube.cells) (edgeID : network.Edge ↪ Fin a.cube.cables)
    (portID : Port ↪ Fin portCount) (originalSite : Fin F.dataDir.entries → network.Site)
    (nativePorts : (Fin F.dataDir.teams × Fin F.dataDir.sites) ↪ Port) (preRegs : Bank w) (usedPin profCost : ℕ)
    (sources : PublishedPin a F.dataDir network cell edgeID portID originalSite nativePorts startup index₀ slot reference dest gap copy copyHeader
      residentFields (pubs agent) mac (active agent).1 ((nodes agent).pins (active agent).1).val.2.1 ((nodes agent).pins (active agent).1).val.2.2 preRegs geo usedPin profCost)
    (epoch : Returns epochPlacement (pubs agent) mac ((nodes agent).pins (active agent).1).val.2.1 ((nodes agent).pins (active agent).1).val.2.2)
    (issuedDir : Returns Packing.Directory.ISA.program (pubs agent) mac epoch.val.2.1 epoch.val.2.2)
    {writerReg writerEnd : Bank w} {after : Memory w} {es : List (TeamRAM.Event w)}
    (writer : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (pubs agent) mac writerReg
      issuedDir.val.2.2 es writerEnd after)
    (written : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner D F.group
      (G.pinLayout agent (F.inputBase agent) (F.columnBase agent) (F.referenceBase agent)) writer)
    (source : F.source origin agent=readings writer.sharedInput)
    (base : Fin 81 → Word w) (packetOrigin cables cellCount rawBase who subtotal fresh areaSlots gateCount outputs width off ell : ℕ)
    (literal : reference.extension=signedProfileExtension a base F.dataDir packetOrigin cables cellCount rawBase who subtotal
      fresh areaSlots gateCount outputs width off ell) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊
    let F₀ := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    PinStart.ChargedPost a.id (fun i => (nodes i).start) budget a startup (6+3*gates+query)
      indexWidth (parameters+scalars) w P₀ L₀ F₀ H₀ active agent := by
  have room : a.after.packed ≤ 2^w := by
    apply le_trans _ sf.addresses.endFit.le
    dsimp only [SignedTaskArena.Layout.endAddress,SignedTaskArena.Layout.entry,DiagonalResidueRAM.gateBase,
      SignedTaskArena.Layout.valuation,SignedTaskArena.Layout.tallyBits,DiagonalTallyAllocation.AfterTasks.localBase,
      DiagonalTallyAllocation.AfterTasks.fresh,DiagonalTallyAllocation.AfterTasks.descriptors,DiagonalTallyAllocation.AfterTasks.refs]
    omega
  have lower : frame+112 ≤ a.cube.header.header := by
    rw [headEq]
    apply Nat.le_trans _ sf.addresses.position
    dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  have words := PreparationFrame.ReturnedOwnershipAt.postInputs a nodes active agent F origin owned startup fields dest
    (6+3*gates+query) indexWidth read index₀ slot reference copy advice residentFields copyHeader sameLayout resident gap
    network cell edgeID portID originalSite nativePorts preRegs usedPin profCost sources epoch issuedDir writer written source
    base packetOrigin cables cellCount rawBase who subtotal fresh areaSlots gateCount outputs width off ell literal room lower
  exact obtained_issued_post a (fun i => (nodes i).start) (active agent) e dir patch row D label recv incoming L home
    payload eb supply privateWidth digits seed F origin ext route active owned rfl issued published banked physicalLayout
    directory marked reported startup fields headEq demand words sf

include owned in
/-- Read the issued report frame on the original recovered writer, including
its native row count. The same prepared report tape then supplies the complete
post. The published extension is the one installed at the signed directory. -/
theorem obtained_writer_post
    {X budget : ℕ} (issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd)
      (copies:=a.cube.teams) (H:=a.p.parameters) (B:=B) a a.id (fun i => (nodes i).start) (active agent) e dir patch row D label recv incoming
      L home payload eb supply privateWidth digits seed)
    (published : PinStart.PublishedArgumentWindow a a.id (fun i => (nodes i).start) (active agent) D label recv incoming X dir.description wp wd
      a.cube.teams a.p.parameters B f R raw budget)
    (banked : e.output=(stages).1.val.2.2)
    (physicalLayout : L=reportLayout a.before a.after frame ctl a.p.parameters a.p.siteWidth a.p.bodyCap a.cube.stop)
    (directory : F.dataDir=dir)
    (marked : ∀ x∈baseReports, ∀ y∈x.bundles, ∀ z∈y.positions, z.parameter<2^w ∧ z.place<w)
    (geometry : FragmentRows.SparseGeometry a f offsets ctl)
    (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    {reserve axes groups cap query guesses gates indexWidth parameters scalars : ℕ} (startup : StartupArena)
    (fields : PositiveFields reserve axes groups cap a.cube.teams a.dim w)
    (headEq : frame=startup.frame) (demand : ℕ)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (sf : a.DeployedFeasiblePost startup dir ctl reserve axes groups cap w query guesses gates indexWidth batch wp wd B X
      ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊ readerTicks (teams+1) parameters scalars)
    (dest : ℕ) (read : BootedPinStart.PublishedSourceReadback a nodes active agent startup fields dest
      (6+3*gates+query) indexWidth)
    (index₀ : Fin startup.teams) (slot : ℕ) (reference : ReferencePacket w pinBits) (copy : BroadcastFrame)
    (advice : AdviceLayout) (residentFields : Pins.ProcessorFields (startup.operands index₀ slot reference).layout)
    (copyHeader : List Bool)
    (sameLayout : (startup.operands index₀ slot reference).layout =
      G.pinLayout agent (args agent).ibase (args agent).hbase (args agent).starbase)
    {geo : Memory w}
    (resident : BootResidence (F:=residentFields) startup index₀ slot reference copy advice (pubs agent)
      (install SparseExterior.driver n (nodes agent).start.routines)
      copyHeader (processorMemory (G.processorFields agent col ext (args agent).ibase (args agent).hbase (args agent).starbase) w)
      (regs agent) (active agent).1 geo)
    (gap : ℕ)
    {netDim portCount : ℕ} {Port : Type} [Fintype Port] {portWidth : Port → ℕ} (network : Network netDim Port portWidth)
    (cell : network.Site → Fin a.cube.cells) (edgeID : network.Edge ↪ Fin a.cube.cables)
    (portID : Port ↪ Fin portCount) (originalSite : Fin F.dataDir.entries → network.Site)
    (nativePorts : (Fin F.dataDir.teams × Fin F.dataDir.sites) ↪ Port) (preRegs : Bank w) (usedPin profCost : ℕ)
    (sources : PublishedPin a F.dataDir network cell edgeID portID originalSite nativePorts startup index₀ slot reference dest gap copy copyHeader
      residentFields (pubs agent) mac (active agent).1 ((nodes agent).pins (active agent).1).val.2.1 ((nodes agent).pins (active agent).1).val.2.2 preRegs geo usedPin profCost)
    (epoch : Returns epochPlacement (pubs agent) mac ((nodes agent).pins (active agent).1).val.2.1 ((nodes agent).pins (active agent).1).val.2.2)
    (issuedDir : Returns Packing.Directory.ISA.program (pubs agent) mac epoch.val.2.1 epoch.val.2.2)
    {writerReg writerEnd : Bank w} {after : Memory w} {es : List (TeamRAM.Event w)}
    (writer : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (pubs agent) mac writerReg
      issuedDir.val.2.2 es writerEnd after)
    (written : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner D F.group
      (G.pinLayout agent (F.inputBase agent) (F.columnBase agent) (F.referenceBase agent)) writer)
    (source : F.source origin agent=readings writer.sharedInput)
    (base : Fin 81 → Word w) (packetOrigin cables cellCount rawBase who subtotal fresh areaSlots gateCount outputs width off ell : ℕ)
    (literal : reference.extension=signedProfileExtension a base dir packetOrigin cables cellCount rawBase who subtotal
      fresh areaSlots gateCount outputs width off ell) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length (teams+1)⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length (teams+1)⌉₊
    let F₀ := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
      (argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    PinStart.ChargedPost a.id (fun i => (nodes i).start) budget a startup (6+3*gates+query)
      indexWidth (parameters+scalars) w P₀ L₀ F₀ H₀ active agent := by
  have counted := PinStart.issued_writer_report_frame a (fun i => (nodes i).start) active agent offsets ctl live ports
    F origin ext route owned writer written source e startup sf.addresses headEq geometry controls home issued.header
    issued.ready issued.place seed issued.allocation
  exact obtained_published_post a nodes active agent e dir patch row D label recv incoming L home payload
    eb supply privateWidth digits seed F origin route owned issued published banked physicalLayout directory marked counted
    startup fields headEq demand sf dest read index₀ slot reference copy advice residentFields copyHeader sameLayout
    resident gap network cell edgeID portID originalSite nativePorts preRegs usedPin profCost sources epoch issuedDir
    writer written source base packetOrigin cables cellCount rawBase who subtotal fresh areaSlots gateCount outputs width
    off ell (by rw [directory]; exact literal)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
