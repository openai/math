import OAI.Computability.BorderVNP.DiagonalIssuedCandidateGeometry
import OAI.Computability.BorderVNP.DiagonalCandidateReportFamily

/-! # The source-specific marked geometry at an actual returned candidate -/

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

variable {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}
    (counts : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
local notation3 (prettyPrint := false) "ret(" u ")" => OpenSuffix.hostImage (base(u)) (readings (out u))
local notation3 (prettyPrint := false) "cs(" u ")" => directoryCells (t.bundleLayout (base(u)) (ctl(u)) d.entries)
  (rows(u)) (report(u)) host (bodyAt(u)) (grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (ret(u))) (counts u)
local notation3 (prettyPrint := false) "roster(" u "," c ")" => (Packing.BundleDirectory.sourceRows host (c).val).map (bodyAt(u))


open SignedTaskArena FragmentRows GeometryAdvice
local notation3 (prettyPrint := false) "directories" => SignedTaskArena.GeometryDirectories.mk
  t.p.sorted t.p.padded t.p.stops t.p.bundlePayload t.p.bundleInverse
set_option maxRecDepth 6500
set_option maxHeartbeats 2600000

/-- Every actual control and report return on the recovered source reads the
emitted owner's original frame, public packet, descriptor ranks and host banks.
The supplied rows are those from the reached source's native storage. -/
theorem ReturnedCandidateReports.issuedGeometry {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (u : Fin (R+1))
    (advance : Returns SignedPrep.controls (ep u) (em u) (er u) (out u))
    (reportRun : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2)
    {banks : CellBanks.Layout} {cur : ReportCursor} {desc : ℕ}
    (alloc : ReportAllocation t.before t.after banks (report(u)) (cs(u)) cur)
    (seed : PreparedReportInput (ep u) advance.val.2.2 (cs(u)) cur desc)
    (startBank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride)
    {fresh fieldHeader gates words bitWidth column : ℕ}
    (dest : origin u=Allocation.dest fresh fieldHeader gates words bitWidth)
    (start : base(u)+112≤fresh) (cap : t.cube.cells≤t.p.report.cells)
    (whole : t.cube.cables*3+(Packing.RoutingOutputs.count t.cube.cables t.cube.cells d.entries (d.teams*d.sites)+
      ((t.cube.cells+(d.entries+t.cube.cells))+(37+(column+2*t.p.padded)))) ≤ words)
    (top : t.cube.header.header=Allocation.stop fresh fieldHeader gates words bitWidth w)
    (sorted : t.p.sorted=ctl(u)+37+column)
    (markers : (directories).MarkerBounds t.cube.cells (readings (site u).geometry))
    (boot : readings (site u).geometry (base(u)+30)=w ∧ readings (site u).geometry (base(u)+14)=t.before.limit ∧
      readings (site u).geometry (base(u)+89)=(t.tasks 0 0 0 0).tasks) :
    let sourceWords := grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (ret(u))
    IssuedGeometry t u.val (ep u 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) w
      (readings (site u).geometry) sourceWords (readings advance.val.2.2) (readings reportRun.val.2.2) := by
  exact (site u).issued_report_geometry N t cell recv size raw u host (bodyAt(u)) (counts u)
    (actual.opened.2 u) (actual.place u) (actual.low u) (actual.reserve u) advance alloc seed reportRun
    dest start cap whole top sorted markers startBank stride (actual.space u) boot

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
