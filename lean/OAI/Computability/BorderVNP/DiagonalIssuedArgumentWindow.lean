import OAI.Computability.BorderVNP.DiagonalPinnedSparseReportSource
import OAI.Computability.BorderVNP.DiagonalPinnedArgumentWindowData

/-! # The clock and the private report roster on the same attained schedule -/

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

open TeamContraction BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator

variable {teams n w : ℕ} (a : SignedTaskArena.Layout)
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix id)

local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "frame" => ((U agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits id U p
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

variable {fit : (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).Fits w
      (readings (PinStart.visits id U p).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
      (PinStart.visits id U p).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
        (PinStart.visits id U p).reports.val.2.2 data i.val)
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
variable (seed : PreparedReportInput ((U agent).pub) (PinStart.visits id U p).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).owner
      (readings e.output)) eb supply privateWidth digits) q dir.description)
local notation "tape" => seed.returnedTape (v).reports
local notation "position" => returnedTapePosition R raw baseReports
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "actualReports" => ((assignedReportReturnEquiv seed mac (v).controls.val.2.1).symm (v).reports).val
local notation "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 5500 in
/-- Physical data saved when the signed arguments were produced on this very
prefix. Its packet, source rows and original marks are independent of the RAM
word array subsequently used to charge their public ownership schedule. -/
structure SparseEmission.IssuedReportData where
  /-- The sparse input retained from this actual argument prefix. -/
  native : PinStart.SparseSource id U p
  /-- The source compiler's original placed cells on this very input. -/
  roster : ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source
  /-- Exact compressed inputs of the compact producer. -/
  owned : native.source.owned=os
  /-- Exact tasks submitted to the native dispatcher. -/
  tasks : native.source.tasks=task
  /-- Order, range, layout and private bounds of the emitted cell packets. -/
  facts : ReachedReportCells (n:=n) e patch row dir.description
  /-- The patched word image at the true typed-arguments cut. -/
  address : patch.built=(stages).2.1.val.2.2
  /-- Original observed processor of each frozen group. -/
  group : Fin a.cube.header.d → Fin (teams+1)
  /-- Native family of all owned-group program returns. -/
  family : TeamRows.Returns (Fin (teams+1)) a.cube w
  /-- The symbols shared by the physical processor histories. -/
  rowBits : Symbols a.cube.header.d → List Bool
  /-- The actual selected route and its source-side observations. -/
  assignment : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) physOwner
  /-- That route has the observed declaration, group owners and tape lengths. -/
  observed : ObservedOwned a.cube D group family physOwner rowBits assignment
  /-- Bit width of the report's physically opened source header. -/
  headerBits : ℕ
  /-- The header of each original bundled source. -/
  header : Fin J → Packing.BottomReports.BundleHeader
  /-- The opened controls and report array fit the selected native arena. -/
  room : a.OpenRoom frame offsets ctl live ports J (2^headerBits) w
  /-- Authentic control placement before the returned reports. -/
  place : OpenSuffix.Placement (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
    a.cube a.before frame (readings (v).owned.val.2.2)
  /-- Physical opened input at the owned program return. -/
  ready : OpenSuffix.Ready (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
    frame (readings (v).owned.val.2.2) w
  /-- Published control pointer read by the sparse emitter. -/
  pointer : readings orig (frame+92)=ctl
  /-- Owner numbers read from the pinned host, before the sparse compiler runs. -/
  ownerWord : ∀ c : Fin a.cube.cells, readings (v).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
    ((physOwner) assignment.1 (label c (chosen a.cube.b a.cube.s assignment.1))).val
  /-- Dimension of the actual sewn network. -/
  dim : ℕ
  /-- Number of static public geometry slots. -/
  sites : ℕ
  /-- Range of the supplied edge numbering. -/
  edges : ℕ
  /-- Range of the supplied port numbering. -/
  portCount : ℕ
  /-- Number of crossing cables in the allocated order. -/
  crossings : ℕ
  /-- Native bit width at each port. -/
  bits : P → ℕ
  /-- The network underlying the transmitted rows. -/
  network : Network dim P bits
  /-- Cell containing each site. -/
  host : network.Site → Fin a.cube.cells
  /-- The physical index of each edge. -/
  edge : network.Edge ↪ Fin edges
  /-- The physical index of each port. -/
  port : P ↪ Fin portCount
  /-- Stable enumeration of crossing cables. -/
  order : network.CrossingEdge host ≃ Fin crossings
  /-- The native cable rows represent the same numbered network. -/
  cables : CableRows network host edge port (f).host (readings orig)
  /-- Original private-entry placement read by the native directory. -/
  privatePlacement : ℕ → ℕ × ℕ
  /-- Live-entry placement read by the same directory. -/
  livePlacement : ℕ → ℕ × ℕ
  /-- The serialized physical raw rows of the fragment emitter. -/
  physicalRows : (List.range (f).count).map ((f).row (readings orig))=dir.directory privatePlacement livePlacement
  /-- Every transmitted bit has its real target and width in the directory. -/
  locations : RowLocations (dir.directory privatePlacement livePlacement) (Fin.val : Fin a.cube.cells → ℕ) recv incoming
  /-- Distinct hidden boxes occupy distinct original input entries. -/
  boxRows : dir.OriginalBoxRows privatePlacement (fun c : Fin a.cube.cells => patch.placed c.val)
  /-- The original source ordinal of each reported bundle. -/
  bundleEntry : Fin J ↪ Fin dir.entries
  /-- A source bundle is delivered to the cell housing its actual site. -/
  sentTo : ∀ j, (privatePlacement (bundleEntry j).val).1=(home j).val
  /-- Positive literal capacity in the transmitted private input. -/
  literal : 0<dir.literal/2
  /-- Original descriptions fit their literal slot. -/
  descriptionFits : dir.description≤dir.literal/2
  /-- Crossing bits fit each selected block of the true host group pair. -/
  pairBound : ∀ pair, load (cablePair order (crossSrc network host) (crossDst network host) label)
    (crossWidth network host ∘ order.symm) pair≤a.cube.header.blocks*(a.cube.h*a.cube.b)
  /-- The real public template, including its physically allocated spare row. -/
  template : LiveWords.Template E I (Fin dir.entries) sites (a.cube.cells+1)
  /-- Cell location of each native public template slot. -/
  site : Fin sites → Fin (a.cube.cells+1)
  /-- Actual values of ordinary geometry parameters. -/
  arg : E → ℕ
  /-- Values of the emitted static operands. -/
  emit : Fin sites → I → ℕ
  /-- Source packets agree with the complete published template. -/
  shape : TypedBatch.SourceFootprint (fun c => patch.placed c.val) (template.directory site arg emit)
  /-- Both sentinels and the full public word sort fit this depth. -/
  publicRoom : (a.cube.cells+1)+template.atoms.length+(a.cube.cells+1)≤2^wp
  /-- Both sentinels and all geometry descriptors fit their sort depth. -/
  descriptorRoom : (a.cube.cells+1)+(Schema.coords template.chunkLabels.length).length+(a.cube.cells+1)≤2^wd
  /-- Every cell has the declared gadget count vector. -/
  counts : ∀ c : Fin a.cube.cells, (patch.placed c.val).reports.length=L.gadgets
  /-- Its published count fields have the native width. -/
  digitsFit : ∀ c : Fin a.cube.cells, ∀ g ∈ (patch.placed c.val).reports, g.length=L.countWidth
  /-- Original box descriptions fit the submitted source rows. -/
  body : ∀ c < (R).cells, (R).owner raw c=(R).team → ∀ j,
    (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length≤dir.description
  /-- Sparse and report programs address the same tail-width table. -/
  tailTable : a.before.tailWidths=L.tailWidths
  /-- Native pre-scan allocation on the physical original rows. -/
  allocation : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl D.1) L baseReports q
  /-- Exact supplemental records emitted from these original report sources. -/
  extras : patch.extra=seedExtras (visitedReportRows R raw baseRow) q
  /-- Each use on an original selected cell belongs to its unique marked power slot. -/
  marks : ((c : {c : Fin a.cube.cells // (group (label c D.1)).val=agent.val}) × UsePositions
    (((baseRow c.val.val).withTape (seed.returnedTape (PinStart.visits id U p).reports) (position c.val.val)).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin copies) (Fin H) B

variable {X budget : ℕ}
    (issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd) (copies:=copies) (H:=H) (B:=B)
      a id U p e dir patch row D label recv incoming L home payload eb supply privateWidth digits seed)
    (published : PinStart.PublishedArgumentWindow a id U p D label recv incoming X dir.description wp wd copies H B
      (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
      (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output) budget)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 5200 in
/-- The funded receipt on the fixed published grouping, fixed public owner RAM,
and fixed saved sparse source. Their other readbacks remain available directly. -/
theorem _root_.OAI.Computability.BorderVNP.RoutingISA.Evaluator.PinStart.issued_argument_at_publication :
    ∃ S : SparseReportSources (Fin dir.entries) E I P a.cube D label recv incoming published.assigned agent.val dir.description
        wp wd copies H B issued.native.source f (readings orig) R raw,
      ProducedRoster a R raw S.places S.geometry S.extra issued.native.source ∧
      PreparedReportInput pub buf (S.reportRows (team:=agent)) q dir.description ∧
      S.LocalReadback (team:=agent) patch.geometry patch.placed patch.extra field (sample) baseReports actualReports ∧
      traceCost (PinStart.afterRoute id U p).val.1+
        privateDirectoryTicks pub (PinStart.afterRoute id U p).val.2.2≤budget := by
  obtain ⟨S,roster,prepared,source⟩ := SparseEmission.sourcesOnScheduledPrefix a id U p e dir patch row D label recv incoming
    published.assigned L home payload eb supply privateWidth digits seed issued.native issued.roster issued.owned issued.tasks
    issued.facts issued.address issued.observed published.scheduled published.image issued.header issued.room issued.place
    issued.ready issued.pointer issued.ownerWord issued.network issued.host issued.edge issued.port issued.order issued.cables
    issued.privatePlacement issued.livePlacement issued.physicalRows issued.locations issued.boxRows issued.bundleEntry
    issued.sentTo issued.literal issued.descriptionFits issued.pairBound issued.template issued.site issued.arg issued.emit
    issued.shape issued.publicRoom issued.descriptorRoom issued.counts issued.digitsFit issued.body issued.tailTable
    issued.allocation issued.extras issued.marks
  exact ⟨S,roster,prepared,source,published.charge (Fin dir.entries) E I P issued.native S roster q prepared⟩

include issued published in
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 5200 in
/-- The schedule, sparse packet, report assignment and argument cost belong to
one reached branch of the pinned native computation. -/
theorem _root_.OAI.Computability.BorderVNP.RoutingISA.Evaluator.PinStart.issued_argument_on_pinned_prefix :
    ∃ prof assigned : ℕ → ℕ, ∃ native : PinStart.SparseSource id U p,
      ∃ S : SparseReportSources (Fin dir.entries) E I P a.cube D label recv incoming assigned agent.val dir.description
        wp wd copies H B native.source f (readings orig) R raw,
        GroupWeights.ScheduleResult (LocalRow.weightLayout a.cube frame D.1.val) (LocalRow.teamLayout a.cube teams) prof assigned ∧
        GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube frame D.1.val) prof a.cube.header.blocks
          a.cube.b a.cube.K a.cube.h D label recv incoming ∧
        (TeamBudget.Layout.mk (teams+1) X a.cube.teamTotals).Passes assigned ∧
        ProducedRoster a R raw S.places S.geometry S.extra native.source ∧
        PreparedReportInput pub buf (S.reportRows (team:=agent)) q dir.description ∧
        S.LocalReadback (team:=agent) patch.geometry patch.placed patch.extra field (sample) baseReports actualReports ∧
        traceCost (PinStart.afterRoute id U p).val.1+
          privateDirectoryTicks pub (PinStart.afterRoute id U p).val.2.2≤budget := by
  obtain ⟨S,roster,prepared,source,cost⟩ := PinStart.issued_argument_at_publication a id U p e dir patch row D label recv
    incoming L home payload eb supply privateWidth digits seed issued published
  exact ⟨published.profile,published.assigned,issued.native,S,published.scheduled,published.image,published.pass,roster,
    prepared,source,cost⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
