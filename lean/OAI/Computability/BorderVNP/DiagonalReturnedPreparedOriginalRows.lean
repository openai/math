import OAI.Computability.BorderVNP.DiagonalOriginalPreparationOnPrefix
import OAI.Computability.BorderVNP.DiagonalSameReportIntervals

/-! # Physical rows of the exact registered returned report -/

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



set_option maxHeartbeats 2800000 in
/-- Match the grouped physical rows with the routed report on the actual
returned candidate. Both the original bundle bits and the report digits are
those of this execution. -/
theorem ReturnedCandidateReports.sourceRows
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out)
      counts (outputs:=outputs) (x:=x) q) (u : Fin (R+1)) :
    SameReportCells (cs(u)) ((source).cells q u) := by
  have identified {cap : ℕ}
      (h : cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s)
      (word : Broadcast t.cube.n t.cube.header.d cap) (range : declarationInRange word)
      (decoded : (Scatter.Assignment.Routed.encode owns q).declaration =
        (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) word.1),fun p j => readCode (cap+1) (word.2 p j))) :
      h ▸ word=broadcast t.cube.b t.cube.s q.1 := by
    subst cap
    exact congrArg Subtype.val ((declared_iff_routeBroadcast t.cube owns ⟨word,range⟩ q).mp decoded)
  have spelling (h : t.cube.header.cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks
      t.cube.b t.cube.h t.cube.s) := identified h raw actual.range actual.declared
  have fixed := (site u).owned_local_reports N t cell recv size raw (origin:=origin u) (ownedPub:=ep u)
    (ownedMac:=em u) (ownedReg:=er u) (out:=out u) state siteID edgeID portID F
    original live u host hdr body factors (bank u) (actual.old u) actual.pin actual.subtotal (actual.literal u)
    (actual.address u) actual.descFit actual.paramFit q spelling slot (actual.opened.2 u) (actual.space u)
    (actual.image u) (actual.net u) actual.codes actual.widths (actual.place u) (actual.low u)
    (actual.reserve u) (actual.rest u) actual.fit (actual.words u) (counts u)
  exact fixed.1

open CompactMachine
variable {n : ℕ} (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (active : PinStart.JointPrefix t.id U)
local notation3 (prettyPrint := false) "visit" u => PinStart.visits t.id U (active u)


local notation3 (prettyPrint := false) "before(" u ")" => OpenSuffix.hostImage (base(u)) (readings (visit u).owned.val.2.2)
local notation3 (prettyPrint := false) "originalRows(" u ")" => directoryCells (t.bundleLayout (base(u)) (ctl(u)) d.entries)
  (rows(u)) (report(u)) host (bodyAt(u)) (grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (before(u))) (counts u)

set_option maxHeartbeats 3000000 in
/-- Read the prepared original report scanner and its actual allocation on
this retained candidate's control return, along with its routed row match. -/
theorem ReturnedCandidateReports.preparedOriginalRows
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=fun k => (U k).pub) (em:=fun k => install SparseExterior.driver n (U k).routines)
      (er:=fun k => (visit k).owned.val.2.1) (out:=fun k => (visit k).owned.val.2.2)
      counts (outputs:=outputs) (x:=x) q) (u : Fin (R+1)) :
    (PreparedReportInput (U u).pub (visit u).controls.val.2.2 (originalRows(u)) t.after.reportCursor d.description ∧
    ReportAllocation t.before t.after (t.cube.cellWriter (base(u)) (ctl(u))
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))) (report(u)) (originalRows(u)) t.after.reportCursor) ∧
    SameReportCells (originalRows(u)) ((source).cells q u) := by
  have same := actual.sourceRows N t cell recv size raw site origin state siteID edgeID portID F
    original live host hdr body factors bank slot counts u
  have ok := actual.opened.1.returns.mp ⟨fun k => (visit k).controls⟩
  have control := actual.opened.2 u
  let s := site u
  have signed := (site u).input
  rw [actual.literal u] at signed
  have pointers := s.receipt.report_input_words t (f u) (actual.old u) (origin u) t.cube.cables t.cube.cells
    actual.pin actual.subtotal s.fresh s.gates s.outputs s.width s.off s.ell s.control s.profile s.claims s.pad raw
    s.actual signed actual.descFit actual.paramFit
  have limits := actual.sourceRoom u
  have bounds := same.physicalRoom limits.1 limits.2
  have receive (j : Fin t.cube.cells) : readings (visit u).owned.val.2.2 ((tables(u)).ends+2*t.cube.cables+j.val)+
      (t.p.report.gadgets*t.p.report.countWidth+weightedCopies (roster(u,j)))≤t.cube.cellStride := by
    rw [control.receive]
    exact (Nat.add_le_add_left (actual.charge u j) _).trans (actual.allocation j)
  have prepared := t.signedReportPreparation (mac:=install SparseExterior.driver n (U u).routines)
    (s:=(visit u).owned.val.2.1) host (bodyAt(u)) (counts u) (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
    d.description control.ready control.placement (actual.space u) control.frame control.controlWord
    (control.report_inputs pointers) control.controls control.frameEnd receive (actual.supp u)
    (actual.marked u) (actual.uses u) (actual.returned ok u same).1 bounds.1 bounds.2
    actual.siteWidth actual.bodyFit actual.endFit
  exact ⟨⟨prepared.2 (visit u).controls,prepared.1⟩,same⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
