import OAI.Computability.BorderVNP.DiagonalCandidateAfterOwned
import OAI.Computability.BorderVNP.DiagonalAdmittedReturnedOwner

/-! # Recovering the actual candidate geometry at an original observed owner -/

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


set_option maxHeartbeats 1600000 in
/-- The observed routing on the original fields supplies the physical
delivery, the same substitutions and the actual terminal owner scan. This
recovers the source families on the native visit before any private check. -/
theorem PreparationFrame.CandidateReportsOnReplay.atOriginalOwner
    (K : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template
      count origin state siteID edgeID portID geom input original live host hdr body factors slot)
    (operands : SharedWords t.cube decl) (q : Matching t.cube owns decl operands.val)
    (scan : TeamRows.Returns (Fin (R+1)) t.cube w)
    (seen : F.OwnedRouteOn fixed t.id owns template total operands q scan) :
    let anchor := (F.replay fixed operands).1
    ∃ bank : Fin (R+1) → Fin d.entries → ℕ → Bool,
    ∃ digits : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool,
      Nonempty (ReturnedCandidateReports N t cell recv size raw (site anchor) origin state siteID edgeID portID geom
        original live host hdr body factors bank (b:=b) (gap:=gap) slot (ep:=scan.pub) (em:=scan.macros)
        (er:=scan.finalRegs) (out:=scan.output) digits (outputs:=outputs) (x:=input anchor) q.val) := by
  obtain ⟨H,delivery,ht,hr,writes,history,substitutions,stored,handoff,owned⟩ := seen
  let same : Matching t.cube owns decl (delivery.receivedRows F.rows F.group) :=
    ⟨q.val,q.property.1,q.property.2.trans stored.symm⟩
  exact K operands H delivery ht hr writes history substitutions stored same scan handoff owned

set_option maxHeartbeats 1600000 in
/-- Use the very native return identified by the parsed field. The candidate
keeps the original report bank and source counts on that return. -/
theorem PreparationFrame.CandidateReportsOnReplay.atOriginalVisit
    (K : F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template
      count origin state siteID edgeID portID geom input original live host hdr body factors slot)
    (operands : SharedWords t.cube decl) (q : Matching t.cube owns decl operands.val)
    (scan : TeamRows.Returns (Fin (R+1)) t.cube w)
    (seen : F.OwnedRouteOn fixed t.id owns template total operands q scan)
    (after : TeamRows.Returns (Fin (R+1)) t.cube w) (atVisit : after=scan) :
    let anchor := (F.replay fixed operands).1
    ∃ bank : Fin (R+1) → Fin d.entries → ℕ → Bool,
    ∃ digits : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool,
      Nonempty (ReturnedCandidateReports N t cell recv size raw (site anchor) origin state siteID edgeID portID geom
        original live host hdr body factors bank (b:=b) (gap:=gap) slot (ep:=after.pub) (em:=after.macros)
        (er:=after.finalRegs) (out:=after.output) digits (outputs:=outputs) (x:=input anchor) q.val) := by
  subst after
  exact PreparationFrame.CandidateReportsOnReplay.atOriginalOwner (K:=K) (seen:=seen)

end TeamContraction

end BorderVNP
end Computability
end OAI
