import OAI.Computability.BorderVNP.DiagonalOriginalObservedCandidateReports
import OAI.Computability.BorderVNP.DiagonalReturnedSourceHostOnPrefix
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved

/-! # Original host bytes of the registered candidate on its own true native return -/

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
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label
  (fun u => report(initialBase,u)) host frozen (fun c => suppliedSize N (fun v => (cell v).val) c)
  (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))
local notation3 (prettyPrint := false) "total" => count+t.cube.header.d.choose 2

local notation3 (prettyPrint := false) "opening(" z "," q "," rows ")" =>
  CandidateReportOpening N t cell recv size raw (site z) origin state host hdr body factors slot q
    (b:=b) (ep:=(rows).pub) (em:=(rows).macros) (er:=(rows).finalRegs) (out:=(rows).output)
local notation3 (prettyPrint := false) "delivered(" z "," q "," rows ")" =>
  CandidateBundleDelivery N t cell recv size raw (site z) origin state host hdr body factors (fun _ _ _ => false)
    slot (fun _ _ _ _ => false) q (out:=(rows).output)
local notation3 (prettyPrint := false) "arguments(" z "," q "," rows ")" =>
  CandidateReportArguments N t cell recv size raw (site z) origin state host hdr body factors (fun _ _ _ => false)
    slot (fun _ _ _ _ => false) q (ep:=(rows).pub) (em:=(rows).macros) (er:=(rows).finalRegs) (out:=(rows).output)

open CompactMachine
set_option maxRecDepth 6500 in
set_option maxHeartbeats 2300000 in
/-- The registered candidate supplies every visited original site on the very same
native owner scan that selected its report memories. -/
theorem PreparationFrame.CandidateReportsOnReplay.hostAtRegisteredVisit
    (K : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw
      positive site template count origin state siteID edgeID portID geom input original live host hdr body factors slot)
    (operands : SharedWords t.cube decl) (q : Matching t.cube owns decl operands.val)
    {inputSize : ℕ} (U : Fin (R+1) → PinStart SparseExterior.driver inputSize w)
    (active : PinStart.JointPrefix t.id U)
    (scan : TeamRows.Returns (Fin (R+1)) t.cube w)
    (same : PinStart.ownedVisits (ar:=t.cube) U active=scan)
    (seen : F.OwnedRouteOn fixed t.id owns template total operands q scan) :
    let anchor := (F.replay fixed operands).1
    let report := fun u => reportLayout t.before t.after (pub anchor u 0).val
      (controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
    let key := fun v : N.Site => (cell v).val
    let semantic := routedSourceReports t.cube N cell owns slot label report host frozen
      (fun c => suppliedSize N key c) (fun c => guessedSize N key c + siteSize N key c (fun v => (state v).size))
    ∀ u : Fin (R+1), ∀ j : Fin d.entries, (∃ c ∈ semantic.cells q.val u, c.number=(host j).val) →
      (frozen j).delivered (report u) d.description
        (FiniteEvaluator.OpenSuffix.hostImage ((U u).pub 0).val (readings (PinStart.visits t.id U (active u)).owned.val.2.2)) ∧
        (frozen j).SiteRoom (report u) w d.description := by
  intro anchor report key semantic u
  obtain ⟨bank,digits,⟨actual⟩⟩ := PreparationFrame.CandidateReportsOnReplay.atOriginalVisit
    (K:=K) (seen:=seen) (atVisit:=same)
  exact actual.sourceHostAtOwnPrefix (U:=U) (active:=active) (u:=u)

end TeamContraction

end BorderVNP
end Computability
end OAI
