import OAI.Computability.BorderVNP.DiagonalReplayCandidateBanks
import OAI.Computability.BorderVNP.DiagonalReplayReportStages

/-! # The retained report checks on the original calendar search -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment JointHeader PackedHistoryCircuit LocalRow Crossing
open DiagonalTallyPacketEmit FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w volume : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (task : SignedTaskArena.Layout)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    {I : Type} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type} {bits : P → ℕ} [Fintype A] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d) (recv : A → Fin task.cube.cells) (amount : A → ℕ)

set_option quotPrecheck false
local notation "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "grp" => declaredTeam ar decl label recv amount R
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "count" => (D.directory pp lp).length
local notation "total" => count+task.cube.header.d.choose 2
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header)
local notation3 (prettyPrint := false) "back" => (HeaderExterior.changeLayout skeleton wire same header).symm


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount
variable {G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
  pub mac reg mem host key sizes N cell label recv amount wire same}

open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs Packing.BottomReports
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open BorderVNP.Cube.MeanChoice BorderVNP.Cube.Physical.NativeAssignments
variable [Fintype P] {origins : Fin (R+1) → ℕ}
    {state : N.Site → Packing.Inherited.Site} {cb lb polyWidth outputs ns np : ℕ} {σ : Type} [Fintype σ]
    {siteID : N.Site ↪ Fin ns} {edgeID : N.Edge ↪ Fin task.cube.cables} {portID : P ↪ Fin np}
    {geom : Fields ns task.cube.cables np task.cube.cells cb lb polyWidth σ} {inp : Fin (R+1) → σ → Bool}
    {original : Fin D.entries → N.Site} {live : Fin (D.teams*D.sites) → P} {home : Fin D.entries → Fin task.cube.cells}
    {hdr : Fin D.entries → BundleHeader} {body factors : Fin D.entries → List CellSparse.Factor}
    {bank : Fin (R+1) → Fin D.entries → ℕ → Bool} {dictionary gap : ℕ}
    {slot : LiveBit N cell ↪ Slot task.cube.n task.cube.header.d task.cube.header.blocks (task.cube.h*task.cube.b)}
    {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}

omit [Fintype P] in
/-- Use the original published geometry, native table and scalar words on the same
processor history as the owned scan. -/
theorem PreparationFrame.SelectedLookupSites.publication_onHistory
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u)
    (data : Nonempty (CandidateReportPublication N task cell recv amount word (chosen.returnedSite x) origins siteID portID geom original live
      (outputs:=outputs) (x:=inp) (b:=dictionary) (gap:=gap))) :
    Nonempty (CandidateReportPublication N task cell recv amount word (chosen.siteOnHistory x H actual) origins siteID portID geom original live
      (outputs:=outputs) (x:=inp) (b:=dictionary) (gap:=gap)) :=
  (chosen.siteOnHistory_iff x H actual (fun _ _ sites => Nonempty (CandidateReportPublication N task cell recv amount word sites origins siteID portID geom original live
      (outputs:=outputs) (x:=inp) (b:=dictionary) (gap:=gap)))).mpr data

omit [Fintype σ] in
/-- Use the public report and packet capacity bounds on the actual owned team. -/
theorem PreparationFrame.SelectedLookupSites.capacity_onHistory
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u)
    (data : Nonempty (CandidateReportCapacity N task cell recv amount word (chosen.returnedSite x) origins state siteID edgeID portID geom
      home hdr body factors bank slot (x:=inp) (gap:=gap))) :
    Nonempty (CandidateReportCapacity N task cell recv amount word (chosen.siteOnHistory x H actual) origins state siteID edgeID portID geom
      home hdr body factors bank slot (x:=inp) (gap:=gap)) :=
  (chosen.siteOnHistory_iff x H actual (fun _ _ sites => Nonempty (CandidateReportCapacity N task cell recv amount word sites origins state siteID edgeID portID geom
      home hdr body factors bank slot (x:=inp) (gap:=gap)))).mpr data

/-- Transfer the controls and their attained incoming RAM back from the observed
team registers to the registered lookup, with the same routed assignment. -/
theorem PreparationFrame.SelectedLookupSites.reportOpening_of_siteOnHistory
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u)
    {q : NativeAssignments.Routed (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h)
      (b:=task.cube.b) (s:=task.cube.s) (greedyOwner R task.cube.b task.cube.s
        (meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d
          ((Nat.succ_pos 1).trans_le (chosen.returnedSite x 0).input.alphabet)) recv amount)}
    (data : CandidateReportOpening N task cell recv amount word (chosen.siteOnHistory x H actual) origins state home hdr body factors slot q
      (b:=dictionary) (ep:=ep) (em:=em) (er:=er) (out:=out)) :
    CandidateReportOpening N task cell recv amount word (chosen.returnedSite x) origins state home hdr body factors slot q
      (b:=dictionary) (ep:=ep) (em:=em) (er:=er) (out:=out) :=
  (chosen.siteOnHistory_iff x H actual (fun _ _ sites => CandidateReportOpening N task cell recv amount word sites origins state home hdr body factors slot q
      (b:=dictionary) (ep:=ep) (em:=em) (er:=er) (out:=out))).mp data

end TeamContraction

end BorderVNP
end Computability
end OAI
