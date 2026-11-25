import OAI.Computability.BorderVNP.DiagonalObservedDispatchReportRows
import OAI.Computability.BorderVNP.DiagonalReturnedPreparedOriginalRows

/-! # The report source and sampled roster on a registered candidate's own return -/

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
open CompactMachine
variable {n : ℕ} (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (active : PinStart.JointPrefix t.id U)
local notation3 (prettyPrint := false) "visit" u => PinStart.visits t.id U (active u)
variable {N t cell recv size raw site origin state siteID edgeID portID F original live host hdr body factors bank slot counts U active}
/-- All six issued-source report readbacks on the recorded calendar lookup's
own physical bank and digits, using its actual pin and returned emitter. -/
theorem ReturnedCandidateReports.reportsAtOwnDispatch
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=fun z => (U z).pub) (em:=fun z => install SparseExterior.driver n (U z).routines)
      (er:=fun z => (visit z).owned.val.2.1) (out:=fun z => (visit z).owned.val.2.2) counts (outputs:=outputs) (x:=x) q)
    {u : Fin (R+1)}
    {fit : (FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (visit u).reports.val.2.2)).Fits w
      (readings (visit u).reports.val.2.2)}
    {cells : t.fragments.cells=(FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (visit u).reports.val.2.2)).cells}
    (emitted : FragmentRows.SparseEmission t _ (visit u).reports.val.2.2 fit cells)
    (pointer : readings (visit u).reports.val.2.2 (((U u).pub 0).val+92)=ctl(u)) :
    DispatchReportRows t u (ports:=d.teams*d.sites) (origin u) (base(u)) host (U u).pub
      (visit u).controls.val.2.2 (bodyAt(u)) (counts u)
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) d.description
      (readings (Packing.Directory.ISA.publish (site u).middle (base(u)) receiving (d.directory pp lp)))
      (readings emitted.output) ((source).cells q u) := by
  have initial := (site u).input
  rw [actual.literal u] at initial
  have entry := (site u).receipt.native_entry t (site u).placement (f u) (actual.old u) (origin u)
    t.cube.cables t.cube.cells actual.pin actual.subtotal (site u).fresh (site u).gates (site u).outputs
    (site u).width (site u).off (site u).ell (site u).control (site u).profile (site u).claims (site u).pad
    raw (site u).actual initial
  rw [actual.address u] at entry
  have stamped := (congrArg (fun m' : Memory w => NativeEntry t.cube (base(u)) (ctl(u))
    (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) R _ (readings m') _) (site u).actual).mp entry
  have prepared := ReturnedCandidateReports.preparedOriginalRows N t cell recv size raw site origin state
    siteID edgeID portID F original live host hdr body factors bank slot counts U active actual u
  exact (visit u).reportsAtMatchingFrame t u (origin u) (base(u)) host hdr body factors (bank u) (counts u)
    (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) d.description stamped (actual.opened.2 u)
    (actual.space u) ((source).cells q u) prepared emitted pointer

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
