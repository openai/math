import OAI.Computability.BorderVNP.DiagonalReplayReportStages
import OAI.Computability.BorderVNP.DiagonalOriginalReportDelivery
import OAI.Computability.BorderVNP.DiagonalCandidateReturnedRouteOwner

/-! # Reading the original delivery on an assigned native report row -/

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


open VPVNP Diagonal.Layout Routing RoutingISA.Transmission Packing TeamContraction.JointHeader
open BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment

variable {r time nPin link inner n : ℕ} {Edge : Type} {G : Wiring R r time nPin link inner n Edge}
    {pin : Fin nPin → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {arrivedDir : Directory.Layout} {actualPP actualLP : ℕ → ℕ × ℕ} {arrivedOwner : ℕ → Fin (R+1)}
    {start stride : ℕ} {H : Fin (R+1) → TeamHistory w} {layout : Fin (R+1) → Pins.Layout}
    {arrived : ReturnedDelivery G pin ext wire arrivedDir actualPP actualLP arrivedOwner start stride H layout}
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {groups : Fin t.cube.header.d → Fin (R+1)} {decl : LengthDeclaration t.cube.n t.cube.header.d}
    {template : DiagonalTallyPacketEmit.Frame} {index : TableEntry t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s → ℕ} {total : ℕ}

private theorem publishedMemory {w R : ℕ} {a : CubeArena.Layout} {frame ctl : ℕ} {axis : Fin (a.n+1)}
    {input written : ℕ → ℕ} {before after : Memory w}
    (entry : NativeEntry a frame ctl axis R input (readings before) written) (returned : before=after) :
    NativeEntry a frame ctl axis R input (readings after) written := returned ▸ entry

private theorem beforeControls (origin cables cells entries live : ℕ) :
    origin+5*cables≤controlsBase origin cables cells entries live+37 := by
  dsimp only [controlsBase,bases]
  omega

/-- The reference-frame receiver and the routed selector agree at each real
cell of a matching declaration. -/
theorem routedOwnerWord_declaredCell {a : CubeArena.Layout} (teams : ℕ) {A : Type} [Fintype A]
    (labels : Fin a.cells → Label (a.n+1) a.header.d) (recv : A → Fin a.cells) (cost : A → ℕ)
    (decl : LengthDeclaration a.n a.header.d)
    (q : NativeAssignments.Routed (blocks:=a.header.blocks) (K:=a.K) (h:=a.h) (b:=a.b) (s:=a.s)
      (greedyOwner teams a.b a.s labels recv cost))
    (matchDecl : Routed.trueDeclaration a.b a.s q.1=decl) (c : Fin a.cells) :
    routedOwnerWord a (greedyOwner teams a.b a.s labels recv cost) labels q c.val =
      (if h : c.val<a.cells then declaredTeam a decl labels recv cost teams (labels ⟨c.val,h⟩ decl.1) else 0).val := by
  rw [routedOwnerWord_at,dite_eq_left c.isLt]
  exact congrArg (fun d' : LengthDeclaration a.n a.header.d =>
    (TeamNative.owner teams (declarationWeight a.header.blocks a.b a.K a.h d' labels recv cost) (labels c d'.1).val).val)
    matchDecl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
/-- In a returned owned-group execution, the geometric addresses from the
publication and the actual pre-scatter words give the marked report read
by each visited row of this same assignment. -/
theorem candidateBundleDelivery_of_returned_originals
    (result : TeamRows.Returns (Fin (R+1)) t.cube w)
    (q : NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K) (h:=t.cube.h) (b:=t.cube.b) (s:=t.cube.s) owns)
    (writer : SharedWriters arrived g src)
    (symbols : SymbolFrame g (src anchor) t.cube.header.blocks t.cube.K t.cube.h decl groups)
    (handoff : OwnedHandoff arrived g src t.cube decl groups template index total result)
    (observed : ObservedOwned t.cube decl groups result owns (arrived.receivedRows g groups) q)
    (actual : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    (capacity : CandidateReportCapacity N t cell recv size raw site origin state siteID edgeID portID F host hdr
      body factors bank slot (x:=x) (gap:=gap))
    (opened : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot
      (b:=b) (ep:=result.pub) (em:=result.macros) (er:=result.finalRegs) (out:=result.output) q)
    (address : host=cell ∘ original)
    (ownerAt : ∀ c : Fin t.cube.cells, routedOwnerWord t.cube owns label q c.val=(arrivedOwner c.val).val)
    (declared : ∀ u, Header (base(u)) (origin u) t.cube.cables t.cube.cells d.entries (readings (site u).geometry))
    (issued : ∀ u : Fin (R+1), OriginalReportDelivery t d N cell original arrivedOwner
      (fun v => (H v).history.val.2.2) (report(u)) (bodyAt(u))) :
    CandidateBundleDelivery N t cell recv size raw site origin state host hdr body factors bank slot counts q (out:=result.output) := by
  subst host
  intro _ u same
  have initial := (site u).input
  rw [actual.literal u] at initial
  have native := (site u).receipt.native_entry t (site u).placement (f u) (actual.old u) (origin u)
    t.cube.cables t.cube.cells actual.pin actual.subtotal (site u).fresh (site u).gates (site u).outputs
    (site u).width (site u).off (site u).ell (site u).control (site u).profile (site u).claims
    (site u).pad raw (site u).actual initial
  rw [actual.address u] at native
  have entry := publishedMemory native (site u).actual
  exact (issued u).hostImage u writer symbols handoff observed same ownerAt entry aux siteID edgeID portID F
    (opened.2 u) (capacity.net u) capacity.codes capacity.widths (declared u) (actual.image u)
    (actual.place u) (actual.low u) (actual.reserve u) ((beforeControls ..).trans (actual.space u).controlEnd)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
