import OAI.Computability.BorderVNP.DiagonalReturnedCandidatePrefixRun
import OAI.Computability.BorderVNP.DiagonalReportCutLayoutCast
import OAI.Computability.BorderVNP.DiagonalOriginalPrefixRuns

/-! # The original selected finite report source at its literal returned prefix -/

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

open CompactMachine CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open SignedTaskArena Physical.NativeLedger Physical.NativeAssignments

set_option maxRecDepth 9000
set_option maxHeartbeats 2200000
set_option autoImplicit false

variable {n : ℕ} (S : PositiveTeam t.id SparseExterior.driver n w) (pr : S.Prefix)
local notation3 (prettyPrint := false) "V" => prefixVisits S pr
local notation3 (prettyPrint := false) "sz" => (S.pub 0).val
local notation3 (prettyPrint := false) "chart(" u ")" => reportLayout t.before t.after sz (ctl(u)) t.p.parameters
  t.p.siteWidth t.p.bodyCap t.cube.stop

local notation3 (prettyPrint := false) "changeAt(" u "," h ")" =>
  congrArg (fun f => reportLayout t.before t.after f (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) h

/-- The exact input of the original prepared execution, using its fixed
common receiving frame and its physical source tape for the same proposed
subtotal. This is evaluated on the chosen return before reindexing its private
rows to the final candidate. -/
theorem ReturnedCandidateReports.originalPrefixRun {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q) (u : Fin (R+1))
    (nu : Fin t.cube.teams) (numberEq : nu.val=u.val)
    (publishedFrame : (ep u 0).val=sz) (owned : out u=(V).owned.val.2.2)
    (cap : d.candidates ≤ t.cube.maxRows)
    (gid : TableEntry t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s → Fin t.p.report.gadgets)
    (assignment : Fin t.cube.header.d → Fin t.cube.teams)
    (path : Path N cell t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.K t.cube.s)
    (fbase : ℕ) (fEq : fbase=sz)
    (r : ReceivedRows (fun _ : Fin t.cube.teams =>
      reportLayout t.before t.after fbase (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) t.cube.cells)
    (proposed : ∀ k, ReportAssignments (r.cells k))
    {res groups capacity width : ℕ} (startup : Fin t.cube.teams → StartupArena)
    (header : PositiveFields res t.cube.n groups capacity t.cube.teams t.dim width)
    (cc : Fin (t.cube.teams*t.dim*width) → Bool)
    (frame : sz=(startup nu).frame)
    (copied : HeaderSeed t (header.withSubtotals cc) S.pub (rawAddress (startup nu) res t.cube.n groups capacity) nu.val (V).owned.val.2.2)
    (prepared : CubePacket.WordPrepared (gadgetLookup t S.pub (Fin.val ∘ assignment) nu.val D
      (pathBanks path t.cube.header.packetBase t.cube.singleBank)) t.id S.pub (V).owned.val.2.2)
    (axis : Fin (t.cube.n+1))
    (allocation : ReportAllocation t.before t.after (t.cube.cellWriter sz (ctl(u)) axis)
      (chart(u)) ((r.atLayout (changeAt(u,fEq))).cells nu) t.after.reportCursor)
    (marks : ∀ c ∈ (r.atLayout (changeAt(u,fEq))).cells nu, ∀ b ∈ c.bundles, ∀ g ∈ b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ) (addresses : t.FinishAddresses (startup nu) (ctl(u)) res t.cube.n groups capacity width w query guesses gates)
    {cur : ReportCursor} {descriptor : ℕ}
    (observed : ReportArgumentCut (V).reports (r.assignmentsAtLayout (changeAt(u,fEq)) proposed nu) cur descriptor)
    {Orig : Type} (patch : ℕ → CellPacket.Placed Orig) (locations : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
    (roster : let parts := (ScheduleClock.argumentVisitsEquiv S.pub (install SparseExterior.driver n S.routines)
      (V).reports.val.2.1 (V).reports.val.2.2).symm (V).arguments
      ∃ input : ScheduleClock.SparseCallInput S.pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster t (t.controlRows nu.val sz (tables(u)).ends (ctl(u)) (tables(u)).livePairs
          (d.teams*d.sites)) (readings parts.1.val.2.2) patch locations extras input)
    (ids : ∀ e,t.id e=(gid e).val) :
    OriginalPrefixRun t header gid assignment path fbase (ctl(u)) t.p.siteWidth t.p.bodyCap startup r nu S pr
      proposed cc := by
  refine ⟨fEq,?_⟩
  rw [r.tapesAtLayout_assignments (changeAt(u,fEq)) proposed]
  exact actual.finishOnPrefix N t cell recv size raw site origin state siteID edgeID portID F original live
    host hdr body factors bank slot counts S pr u nu numberEq publishedFrame owned cap gid assignment path
    (r.atLayout (changeAt(u,fEq))) (r.assignmentsAtLayout (changeAt(u,fEq)) proposed) (startup nu)
    (header.withSubtotals cc) frame copied prepared axis allocation marks query guesses gates addresses
    observed patch locations extras roster ids

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
