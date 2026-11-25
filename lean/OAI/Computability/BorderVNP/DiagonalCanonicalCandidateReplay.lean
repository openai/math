import OAI.Computability.BorderVNP.DiagonalProjectedReportObservation
import OAI.Computability.BorderVNP.DiagonalReplayReportAssembly

/-! # The report opening and full report family at the selected physical writer -/

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
local notation3 (prettyPrint := false) "opening(" z "," q "," rows ")" =>
  CandidateReportOpening N t cell recv size raw (site z) origin state host hdr body factors slot q
    (b:=b) (ep:=(rows).pub) (em:=(rows).macros) (er:=(rows).finalRegs) (out:=(rows).output)
local notation3 (prettyPrint := false) "test(" side ")" =>
  F.ReportTest (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template count origin
    state siteID edgeID portID geom input original live host hdr body factors slot side
local notation3 (prettyPrint := false) "total" => count+t.cube.header.d.choose 2
local notation3 (prettyPrint := false) "assembled(" z "," q "," run ")" =>
  (∃ bank : Fin (R+1) → Fin d.entries → ℕ → Bool,
   ∃ digits : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool,
     Nonempty (ReturnedCandidateReports N t cell recv size raw (site z) origin state siteID edgeID portID geom
       original live host hdr body factors bank (b:=b) (gap:=gap) slot (ep:=(run).pub) (em:=(run).macros)
       (er:=(run).finalRegs) (out:=(run).output) digits (outputs:=outputs) (x:=input z) q))

variable {nativeFrame : ℕ} {dst ib hb sb : Fin (R+1) → ℕ}
    {epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u)}
    {published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2}
    {endReg : HeaderExterior L header → Fin (R+1) → Bank w} {out : HeaderExterior L header → Fin (R+1) → Memory w}
    {events : HeaderExterior L header → Fin (R+1) → List (TeamRAM.Event w)}
    {W : ∀ x u, WriterHistory t.cube.n (selectorWidth t.cube.n t.cube.K t.cube.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u)}
    (picked : PreparationFrame.WriterProjection G L t.cube d pp lp representative
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun pair j => readCode (t.cube.header.cap+1) (raw.2 pair j))
      group nativeFrame header
      pin guess dst ib hb sb pub mac reg mem epoch published endReg out events W F)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
/-- The opening test can read the canonical wiring and writer on the very
owned return under examination. -/
theorem PreparationFrame.ReportTest.opening_ofCanonical
    (handle : picked.CanonicalReportReplay fixed owns template t.id total (fun z q run => opening(z,q,run))) :
    test(.opening) := by
  exact picked.observeReportReplay fixed owns template t.id total (fun z q run => opening(z,q,run)) handle

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
/-- Reassemble the full report family at its original output registers and
memory using a handler on the chosen physical native writer. -/
theorem PreparationFrame.CandidateReportsOnReplay.ofCanonical
    (handle : picked.CanonicalReportReplay fixed owns template t.id total (fun z q run => assembled(z,q,run))) :
    F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site
      template count origin state siteID edgeID portID geom input original live host hdr body factors slot := by
  exact picked.observeReportReplay fixed owns template t.id total (fun z q run => assembled(z,q,run)) handle

end TeamContraction

end BorderVNP
end Computability
end OAI
