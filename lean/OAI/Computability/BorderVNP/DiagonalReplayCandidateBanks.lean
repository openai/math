import OAI.Computability.BorderVNP.DiagonalCandidatePublicBank
import OAI.Computability.BorderVNP.DiagonalSelectedLookupBuilders

/-! # The original candidate on the returned routing processors -/

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
    {I : Type*} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type*} {bits : P → ℕ} [Fintype A] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
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

/-- Read the original signed candidate using the public registers recorded
by the very same received team history. -/
noncomputable def PreparationFrame.SelectedLookupSites.siteOnHistory
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u) (u : Fin (R+1)) :=
  (chosen.returnedSite x u).rebankPublic (actual u).1 (actual u).2.1

/-- The geometry return, private placement, control pointer and shared writer
are the original attained reads after fixing the team memory. -/
theorem PreparationFrame.SelectedLookupSites.siteOnHistory_stages
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u) (u : Fin (R+1)) :
    let physical := chosen.siteOnHistory x H actual u
    let registered := chosen.returnedSite x u
    physical.geometry=registered.geometry ∧ physical.middle=registered.middle ∧ physical.old=registered.old ∧
    physical.control=registered.control ∧ physical.receipt.history.dataInput=registered.receipt.history.dataInput ∧
    physical.receipt.history.sharedInput=registered.receipt.history.sharedInput ∧
    F.source x u=readings physical.receipt.history.sharedInput := by
  obtain ⟨first,medium,previous,control,data,shared⟩ := (chosen.returnedSite x u).rebankPublic_fields
    (actual u).1 (actual u).2.1
  exact ⟨first,medium,previous,control,data,shared,(chosen.projection.image x u).trans (congrArg readings shared).symm⟩

/-- Any dependent report check on the observed public registers proves the
same check on the registered sites, retaining its true control return. -/
theorem PreparationFrame.SelectedLookupSites.siteOnHistory_iff
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u)
    (test : ∀ (front : Fin (R+1) → Arg → Word w) (routines : Fin (R+1) → TeamOpcode.Macros w 8),
      (∀ u, CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase (PL u)
        (G.processorFields u pin (back x).val (ib u) (hb u) (sb u)) (BF u) (guess u) (front u)
        (routines u) (reg (back x) u) (mem (back x) u) host key sizes N cell recv amount) → Prop) :
    test (fun u => (H u).pub) (fun u => (H u).macros) (chosen.siteOnHistory x H actual) ↔
      test ((pub ∘ back) x) ((mac ∘ back) x) (chosen.returnedSite x) := by
  have transport {front : Fin (R+1) → Arg → Word w} {routines : Fin (R+1) → TeamOpcode.Macros w 8}
      (frontEq : ∀ u, front u=(pub ∘ back) x u) (routinesEq : ∀ u, routines u=(mac ∘ back) x u) :
      test front routines (fun u => (chosen.returnedSite x u).rebankPublic (frontEq u) (routinesEq u)) ↔
        test ((pub ∘ back) x) ((mac ∘ back) x) (chosen.returnedSite x) := by
    have sameFront := funext frontEq
    have sameRoutines := funext routinesEq
    subst front routines
    rfl
  exact transport (fun u => (actual u).1) (fun u => (actual u).2.1)

end TeamContraction

end BorderVNP
end Computability
end OAI
