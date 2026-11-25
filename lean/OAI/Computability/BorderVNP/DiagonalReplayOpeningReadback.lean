import OAI.Computability.BorderVNP.DiagonalReplayReportStages
import OAI.Computability.BorderVNP.DiagonalCandidateControlTests

/-! # Read the observed opener at its common published frame -/

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


/-- A common physical opener provides the controls and exact owned memory at
every selected processor, with its published frame and geometry origin. -/
theorem candidateReportOpening_of_readback
    (q : NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K)
      (h:=t.cube.h) (b:=t.cube.b) (s:=t.cube.s) owns)
    (atOrigin : ℕ) (origins : ∀ u, origin u=atOrigin) (count : ℕ) :
    let tables := bases atOrigin t.cube.cables t.cube.cells d.entries
    let ctrl := controlsBase atOrigin t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
    let physical := fun u : Fin (R+1) => t.openInputs u.val initialBase tables.ends ctrl tables.livePairs
      (d.teams*d.sites) d.entries b host hdr
    (OpenSuffix.ControlFamily physical ep em er out (NativeAssignments.RoutedPins N cell owns slot q) ∧
      ∀ u, FrozenControlReadback t (physical u) u.val initialBase (ep u 0).val ctrl tables.ends tables.livePairs
        (d.teams*d.sites) d.entries count w (fun c => suppliedSize N cell c)
        (readings (site u).receipt.history.dataInput) (readings (out u))) →
    CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot
      (b:=b) (ep:=ep) (em:=em) (er:=er) (out:=out) q := by
  intro ptr ctl physical observed
  have eqProg (u : Fin (R+1)) : prog(u)=physical u := by
    dsimp only [physical,ctl,ptr]
    rw [(site u).origin,origins u]
  refine ⟨?_,fun u => ?_⟩
  · change OpenSuffix.ControlFamily (fun u : Fin (R+1) => prog(u)) ep em er out _
    rw [show (fun u : Fin (R+1) => prog(u))=physical from funext eqProg]
    exact observed.1
  · change FrozenControlEntry t (prog(u)) (base(u)) (ep u 0).val (ctl(u)) (tables(u)).ends w _ _ _
    rw [eqProg u,(site u).origin,origins u]
    exact (observed.2 u).owned

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
