import OAI.Computability.BorderVNP.DiagonalCandidateAfterOwned
import OAI.Computability.BorderVNP.DiagonalRecoveredFrameCandidate

/-! # The actual returned report certificate of the chosen source prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction
open Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open _root_.OAI.Computability.BorderVNP.Cube Physical Tally MeanChoice GroupWeights LocalRow SignedPrep DiagonalTallyPacketEmit
open Crossing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open Packing.BottomReports DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory

variable {D w R X r teams pinsCount link inner n : ℕ} {Edge : Type} {G : Wiring R r teams pinsCount link inner n Edge}
    {L : WireLayout (R+1) r link} {header : List Bool} {pin : Fin pinsCount → Bool} (fixed : Block (R+1))
    (t : SignedTaskArena.Layout) {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin t.cube.cells) (recv : A → Fin t.cube.cells) (size : A → ℕ)
    {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {initialBase receiving : ℕ} {pins : Fin (R+1) → Pins.Layout}
    {fields : HeaderExterior L header → (u : Fin (R+1)) → Pins.ProcessorFields (pins u)}
    {bf : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool} {I : Type*} [Fintype I]
    {resides : I → Fin t.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap) (positive : 0<t.cube.header.d)
    (site : ∀ z u, CandidateSite (X:=X) t.cube d pp lp raw representative
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      group initialBase receiving (pins u) (fields z u) (bf u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides key sizes N cell recv size)
    (F : PreparationFrame G L t.cube
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      header pin pub mac reg mem)
    (template : Frame) (origin : Fin (R+1) → ℕ)
    {cb lb widthO outputs ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Packing.Inherited.Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (geom : Fields ns t.cube.cables np t.cube.cells cb lb widthO σ)
    (input : HeaderExterior L header → Fin (R+1) → σ → Bool)
    (original : Fin d.entries → N.Site) (live : Fin (d.teams*d.sites) → P)
    (host : Fin d.entries → Fin t.cube.cells) (hdr : Fin d.entries → BundleHeader)
    (body factors : Fin d.entries → List CellSparse.Factor) {b gap : ℕ}
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))

local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d positive
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s label recv size
local notation3 (prettyPrint := false) "frozen" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
local notation3 (prettyPrint := false) "report(" x "," u ")" => reportLayout t.before t.after x (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label
  (fun u => report(initialBase,u)) host frozen (fun c => suppliedSize N (fun v => (cell v).val) c)
  (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))

variable (builders : F.Builders fixed t.id (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size)) (agree : F.SourceAgreement fixed (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))) builders)
  (q : {v : Declared t.cube (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))) // (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))).pins v.val}) (reports : (routedSourceReports t.cube N cell (greedyOwner R t.cube.b t.cube.s (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive) recv size) slot (meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d positive)
    (fun u : Fin (R+1) => reportLayout t.before t.after initialBase (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop) host (fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false))
    (fun c => suppliedSize N (fun v => (cell v).val) c) (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))).actual q.val.val)
  (publication : F.LookupPublication t)
local notation3 (prettyPrint := false) "slots" =>
  (publication.directory.directory publication.privatePlacement publication.livePlacement).length+t.cube.header.d.choose 2
local notation3 (prettyPrint := false) "operands" => declaredWords t.cube owns decl q.val
local notation3 (prettyPrint := false) "replayZ" => F.replay fixed operands
local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed source builders agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "vis" => fun u => (visitsEquiv t.id (pub full.1 u) (mac full.1 u)
  (reg full.1 u) (mem full.1 u)).symm (full.2 u)
local notation3 (prettyPrint := false) "scan" => visitedOwnedScans (ar:=t.cube) vis

set_option maxHeartbeats 2200000
set_option maxRecDepth 8500
set_option autoImplicit false

/-- The candidate selected by the admitted frame on the replay's actual
owned row run is available on the exact control state of this source inverse.
It carries the actual writer, typed source roster and per-team sparse program
used by the same machine before any report check. -/
theorem PreparationFrame.sourceEquiv_returnedCandidate
    (reached : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template
      (publication.directory.directory publication.privatePlacement publication.livePlacement).length origin
      state siteID edgeID portID geom input original live host hdr body factors slot)
    (common : ∀ u,readings (pub replayZ.1 u) 0=publication.frame)
    (room : t.after.packed ≤ 2^w) (values : CubeConstants.valueBound t.id<2^w)
    (space : t.cube.ReplayRoom w publication.frame)
    (scanner : ∀ u : Fin (R+1),t.cube.ScannerWords (readings (pub replayZ.1 u) 0) u.val (decl).1.val
      (fun j => (F.group j).val) (readings (pub replayZ.1 u)) (F.source replayZ.1 u) (decl).2)
    (constant : ∀ u,CubeConstants.Fields
      (CubeConstants.inArena template t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (readings (pub replayZ.1 u) 0) (CubeConstants.idBase t.cube.stop t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s)
      (F.source replayZ.1 u))
    (scheduled : F.group=owns q.val.val.1) :
    ∃ bank : Fin (R+1) → Fin d.entries → ℕ → Bool,
      ∃ digits : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool,
        Nonempty (ReturnedCandidateReports N t cell recv size raw (site full.1) origin state siteID edgeID portID geom
          original live host hdr body factors bank (b:=b) (gap:=gap) slot (ep:=(scan).pub) (em:=(scan).macros)
          (er:=(scan).finalRegs) (out:=(scan).output) digits (outputs:=outputs) (x:=input full.1) q.val.val) := by
  let record (anchor : HeaderExterior L header) (route : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns)
      (run : TeamRows.Returns (Fin (R+1)) t.cube w) :=
    ∃ bank : Fin (R+1) → Fin d.entries → ℕ → Bool,
      ∃ digits : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool,
        Nonempty (ReturnedCandidateReports N t cell recv size raw (site anchor) origin state siteID edgeID portID geom
          original live host hdr body factors bank (b:=b) (gap:=gap) slot (ep:=run.pub) (em:=run.macros)
          (er:=run.finalRegs) (out:=run.output) digits (outputs:=outputs) (x:=input anchor) route)
  exact F.sourceEquiv_recovered_candidate t fixed source builders agree q reports publication template record
    reached common room values space scanner constant scheduled

end TeamContraction

end BorderVNP
end Computability
end OAI
