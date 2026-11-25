import OAI.Computability.BorderVNP.DiagonalIssuedGeometryOnPrefix
import OAI.Computability.BorderVNP.DiagonalReplayReportStages

/-! # The marked source packet consumed by the issued report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Physical MeanChoice GroupWeights LabelIndex Tally
open TeamContraction JointHeader LocalRow Transmission VPVNP.BurstRAM PackedHistoryCircuit
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open scoped Classical

open GeometryAdvice

/-- Scalar operands and marker bounds of the selected source packet, all
read on its original profile RAM. -/
structure ReportTaskImage (task : SignedTaskArena.Layout) (entries activePorts base origin word : ℕ)
    (mem : ℕ → ℕ) : Prop where
  /-- Extents of the complete published packet, including the inverse ranks. -/
  extents : ∃ fresh cap gates outputs field column,
    origin=Allocation.dest fresh cap gates outputs field ∧ base+112≤fresh ∧
    task.cube.cells≤task.p.report.cells ∧
    task.cube.cables*3+(Packing.RoutingOutputs.count task.cube.cables task.cube.cells entries activePorts+
      ((task.cube.cells+(entries+task.cube.cells))+(37+(column+2*task.p.padded))))≤outputs ∧
    task.cube.header.header=Allocation.stop fresh cap gates outputs field word ∧
    task.p.sorted=controlsBase origin task.cube.cables task.cube.cells entries activePorts+37+column
  /-- Stored ranks in the selected descriptor section. -/
  markers : (SignedTaskArena.GeometryDirectories.mk task.p.sorted task.p.padded task.p.stops
    task.p.bundlePayload task.p.bundleInverse).MarkerBounds task.cube.cells mem
  /-- Early physical task words retained on this same memory. -/
  words : mem (base+30)=word ∧ mem (base+14)=task.before.limit ∧ mem (base+89)=(task.tasks 0 0 0 0).tasks

variable {D w R X : ℕ} {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells)
    (recv : A → Fin t.cube.cells) (size : A → ℕ) {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : Fin (R+1) → Bank w} {mem : Fin (R+1) → Memory w}
    {initialBase receiving : ℕ} {pins : Fin (R+1) → Pins.Layout} {fields : (u : Fin (R+1)) → Pins.ProcessorFields (pins u)}
    {f : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool} {I : Type*} [Fintype I]
    {resides : I → Fin t.cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    {owner : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
    (site : ∀ u, CandidateSite (X:=X) t.cube d pp lp raw owner
      (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
        (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j)))
      group initialBase receiving (pins u) (fields u) (f u) (guess u) (pub u) (mac u) (reg u) (mem u)
      resides keyID sizes N cell recv size)
    (origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "base(" u ")" => (pub u 0).val
local notation3 (prettyPrint := false) "tables(" u ")" => bases (origin u) t.cube.cables t.cube.cells d.entries
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d ((Nat.succ_pos 1).trans_le (site 0).input.alphabet)
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s label recv size
variable {cb lb polyWord outputs ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (F : Fields ns t.cube.cables np t.cube.cells cb lb polyWord σ) {x : Fin (R+1) → σ → Bool}
    (original : Fin d.entries → N.Site) (live : Fin (d.teams*d.sites) → P)
    (host : Fin d.entries → Fin t.cube.cells) (hdr : Fin d.entries → BundleHeader)
    (body factors : Fin d.entries → List CellSparse.Factor) (bank : Fin (R+1) → Fin d.entries → ℕ → Bool)
    {b gap : ℕ} (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))
variable {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}
    (counts : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)

open CompactMachine CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open SignedTaskArena Physical.NativeAssignments GeometryAdvice Evaluator.ScheduleClock

set_option maxHeartbeats 2200000
set_option maxRecDepth 7000

section OriginalReport

local notation3 (prettyPrint := false) "bodyAt(" u ")" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (bank u j)
local notation3 (prettyPrint := false) "frozen" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "key" => fun v : N.Site => (cell v).val
local notation3 (prettyPrint := false) "aux" => fun v : N.Site => Site.size (state v)
local notation3 (prettyPrint := false) "report(" u ")" => reportLayout t.before t.after (base(u)) (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label (fun u => report(u))
  host frozen (fun c => suppliedSize N key c) (fun c => guessedSize N key c+siteSize N key c aux)
local notation3 (prettyPrint := false) "prog(" u ")" => t.openInputs (u).val (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs
  (d.teams*d.sites) d.entries b host hdr
local notation3 (prettyPrint := false) "rows(" u ")" => t.controlRows (u).val (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites)

local notation3 (prettyPrint := false) "ret(" u ")" => OpenSuffix.hostImage (base(u)) (readings (out u))
local notation3 (prettyPrint := false) "cs(" u ")" => directoryCells (t.bundleLayout (base(u)) (ctl(u)) d.entries)
  (rows(u)) (report(u)) host (bodyAt(u)) (grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (ret(u))) (counts u)

/-- The original local control and report visit already provide the physical
geometry used by its private argument, before an argument return exists. -/
theorem issuedGeometryOnReport
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (publication : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    (opening : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot q
      (b:=b) (ep:=ep) (em:=em) (er:=er) (out:=out))
    (u : Fin (R+1))
    (advance : Returns SignedPrep.controls (ep u) (em u) (er u) (out u))
    (reportRun : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2)
    {banks : CellBanks.Layout} {cur : ReportCursor} {desc : ℕ}
    (alloc : ReportAllocation t.before t.after banks (report(u)) (cs(u)) cur)
    (seed : PreparedReportInput (ep u) advance.val.2.2 (cs(u)) cur desc)
    (startBank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride)
    (packet : ReportTaskImage t d.entries (d.teams*d.sites) (base(u)) (origin u) w (readings (site u).geometry)) :
    let sourceWords := grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (ret(u))
    IssuedGeometry t u.val (ep u 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) w
      (readings (site u).geometry) sourceWords (readings advance.val.2.2) (readings reportRun.val.2.2) := by
  obtain ⟨fresh,cap,gates,words,field,column,dest,low,fits,total,stop,sorted⟩ := packet.extents
  exact (site u).issued_report_geometry N t cell recv size raw u host (bodyAt(u)) (counts u)
    (opening.2 u) (publication.place u) (publication.low u) (publication.reserve u) advance alloc seed reportRun
    dest low fits total stop sorted packet.markers startBank stride (publication.space u) packet.words

end OriginalReport

variable {n : ℕ} (U : Fin (R+1) → PinStart SparseExterior.driver n w) (active : PinStart.JointPrefix t.id U)
    (u : Fin (R+1))

local notation3 (prettyPrint := false) "V" => PinStart.visits t.id U (active u)
local notation3 (prettyPrint := false) "mp" => (V).reports.val.2.2
local notation3 (prettyPrint := false) "core" => (U u).pub
local notation3 (prettyPrint := false) "code" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "sc" => FragmentRows.Layout.fromFrame (core 0).val (readings mp)
local notation3 (prettyPrint := false) "steps" => (argumentVisitsEquiv core code (V).reports.val.2.1 mp).symm (V).arguments
local notation3 (prettyPrint := false) "up" => receiving+7*d.candidates
local notation3 (prettyPrint := false) "dst" => Allocation.dest up (site u).profile.length (site u).gates (site u).outputs (site u).width
local notation3 (prettyPrint := false) "dataRows" => (d.directory pp lp).length


local notation3 (prettyPrint := false) "bodyAt(" u ")" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (bank u j)
local notation3 (prettyPrint := false) "report(" u ")" => reportLayout t.before t.after (base(u)) (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "nativeControl" => (V).controls.val.2.2
local notation3 (prettyPrint := false) "input" => OpenSuffix.hostImage (base(u)) (readings (V).owned.val.2.2)
local notation3 (prettyPrint := false) "sourceWords" => grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries)
  host (bodyAt(u)) input
local notation3 (prettyPrint := false) "scan" => t.controlRows u.val (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites)
local notation3 (prettyPrint := false) "rows₀" => directoryCells (t.bundleLayout (base(u)) (ctl(u)) d.entries) scan
  (report(u)) host (bodyAt(u)) sourceWords (counts u)
local notation3 (prettyPrint := false) "directories" => SignedTaskArena.GeometryDirectories.mk
  t.p.sorted t.p.padded t.p.stops t.p.bundlePayload t.p.bundleInverse

/-- Before any sparse argument has been constructed, the earlier report
publication and reached opening already give its complete native geometry
on the original team's two consecutive control and report returns. -/
theorem issuedGeometryOnPublishedPrefix
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (publication : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    (opening : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot q
      (b:=b) (ep:=fun z => (U z).pub) (em:=fun z => install SparseExterior.driver n (U z).routines)
      (er:=fun z => (PinStart.visits t.id U (active z)).owned.val.2.1)
      (out:=fun z => (PinStart.visits t.id U (active z)).owned.val.2.2))
    {banks : CellBanks.Layout} {cur : ReportCursor} {desc : ℕ}
    (alloc : ReportAllocation t.before t.after banks (report(u)) rows₀ cur)
    (seed : PreparedReportInput core nativeControl rows₀ cur desc)
    (startBank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride)
    (packet : ReportTaskImage t d.entries (d.teams*d.sites) (base(u)) (origin u) w (readings (site u).geometry)) :
    IssuedGeometry t u.val (core 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) w
      (readings (site u).geometry) sourceWords (readings nativeControl) (readings mp) := by
  exact issuedGeometryOnReport N t cell recv size raw site origin state siteID portID F original live
    host hdr body factors bank slot counts publication opening u (V).controls (V).reports alloc seed startBank stride packet

/-- On the original report and owned return, one geometry packet supplies
every descriptor bound and startup word used by the sparse argument. -/
theorem ReturnedCandidateReports.issuedGeometryFromPacket
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (pubAt : (ep u 0).val=(core 0).val) (owned : out u=(V).owned.val.2.2)

    {banks : CellBanks.Layout} {cur : ReportCursor} {desc : ℕ}
    (alloc : ReportAllocation t.before t.after banks (report(u)) rows₀ cur)
    (seed : PreparedReportInput core nativeControl rows₀ cur desc)
    (startBank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride)
    (packet : ReportTaskImage t d.entries (d.teams*d.sites) (base(u)) (origin u) w (readings (site u).geometry)) :
    IssuedGeometry t u.val (core 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) w
      (readings (site u).geometry) sourceWords (readings nativeControl) (readings mp) := by
  obtain ⟨fresh,cap,gates,words,field,column,dest,low,fits,total,stop,sorted⟩ := packet.extents
  exact actual.issuedGeometryOnPrefix N t cell recv size raw site origin state siteID edgeID portID F original live
    host hdr body factors bank slot counts U active u pubAt owned alloc seed startBank stride
    dest low fits total stop sorted packet.markers packet.words

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
