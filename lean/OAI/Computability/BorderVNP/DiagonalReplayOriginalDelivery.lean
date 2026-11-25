import OAI.Computability.BorderVNP.DiagonalReplayReportAssembly
import OAI.Computability.BorderVNP.DiagonalCandidateOriginalDelivery

/-! # Original bundle delivery throughout a returned replay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

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
    (template : Frame) (count : ℕ) (origin : Fin (R+1) → ℕ)
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

local notation3 (prettyPrint := false) "verified" step =>
  F.ReportTest (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template count
    origin state siteID edgeID portID geom input original live host hdr body factors slot step

set_option maxRecDepth 6500 in
set_option maxHeartbeats 2200000 in
/-- Transport every assigned original through the actual report execution
selected by the replay. The public directory, capacity and opening all
come from this frame at the current exterior and matching assignment. -/
theorem PreparationFrame.bundleDeliveryOnReplay
    (publication : verified .publication) (capacity : verified .capacity) (opening : verified .opening)
    (address : host=cell ∘ original)
    (receivers : F.cellOwner=fun n => if h : n<t.cube.cells then
      declaredTeam t.cube decl label recv size R (label ⟨n,h⟩ (decl).1) else 0)
    (caps : ∀ x u, Packing.RoutingOutputs.Header (pub x u 0).val (origin u) t.cube.cables
      t.cube.cells d.entries (readings (site x u).geometry))
    (issued : ∀ (operands : SharedWords t.cube decl), let z := F.replay fixed operands
      ∀ (H : Fin (R+1) → TeamHistory w), ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement
        F.cellOwner F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)) →
      ∀ u : Fin (R+1), OriginalReportDelivery t d N cell original F.cellOwner (fun j => (H j).history.val.2.2)
        (report((pub z.1 u 0).val,u)) frozen) :
    verified .delivery := by
  intro operands z H delivery table records writer states substitution writes matched result handoff observed
  obtain ⟨published⟩ := publication z.1
  obtain ⟨bound⟩ := capacity z.1 matched.val
  have entered := opening operands H delivery table records writer states substitution writes matched result handoff observed
  refine candidateBundleDelivery_of_returned_originals (counts:=fun _ _ _ _ => false) (result:=result) (q:=matched.val) (writer:=writer)
    (symbols:=F.frame z.1) (handoff:=handoff) (observed:=observed) (actual:=published) (capacity:=bound)
    (opened:=entered) (address:=address) (ownerAt:=?_) (declared:=caps z.1) (issued:=issued operands H delivery)
  intro c
  exact (routedOwnerWord_declaredCell _ _ _ _ _ _ matched.property.1 c).trans
    (congrArg Fin.val (congrFun receivers c.val)).symm

end TeamContraction

end BorderVNP
end Computability
end OAI
