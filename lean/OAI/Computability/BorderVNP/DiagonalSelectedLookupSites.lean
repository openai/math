import OAI.Computability.BorderVNP.DiagonalCandidateLookupPublication

/-! # Keeping each attained signed site when forming an admissible lookup frame -/

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
/-- The calibrated publication and its actual per-site observations,
retained together when selecting an admissible frame. -/
structure PreparationFrame.SelectedLookupSites
    (F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back))
    (evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop) where
  /-- One physically returned signed processor at each exterior and team. -/
  site : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u)
  attained : ∀ x u, evidence x u (site x u)
  projection : PreparationFrame.WriterProjection G wire ar D pp lp owner decl grp frame header pin guess dst ib hb sb
      (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
      (fun x u => (site (back x) u).published) (fun x u => (site (back x) u).receipt.endReg) (fun x u => (site (back x) u).receipt.out)
      (fun x u => (site (back x) u).receipt.events) (fun x u => (site (back x) u).receipt.history) F

variable {G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
  pub mac reg mem host key sizes N cell label recv amount wire same}

/-- Read the publication of the selected family at its true epoch, directory
return, and complete shared-writer run. -/
noncomputable abbrev PreparationFrame.SelectedLookupSites.publication
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence) : F.LookupPublication task :=
  chosen.projection.candidatePublication G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase
    owner word pub mac reg mem host key sizes N cell label recv amount wire same chosen.site F

/-- The original signed candidate whose returns run at this exterior on the
chosen wire. The input remains the one before the layout was widened. -/
noncomputable abbrev PreparationFrame.SelectedLookupSites.returnedSite
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence) (x : HeaderExterior wire header) (u : Fin (R+1)) :=
  chosen.site (back x) u

/-- In the chosen frame, the original per-pin evidence and all shared-writer
stages refer to exactly the same return, including the memory from which
the frame reads its source words. -/
theorem PreparationFrame.SelectedLookupSites.returnedSiteStages
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence) (x : HeaderExterior wire header) (u : Fin (R+1)) :
    evidence (back x) u (chosen.returnedSite x u) ∧
    chosen.publication.epoch x u=(chosen.returnedSite x u).epoch ∧
    chosen.publication.published x u=(chosen.returnedSite x u).published ∧
    chosen.publication.history x u=(chosen.returnedSite x u).receipt.history ∧
    F.source x u=readings (chosen.returnedSite x u).receipt.history.sharedInput :=
  ⟨chosen.attained _ _,rfl,rfl,rfl,chosen.projection.image x u⟩

/-- The common frame address remains the physical address used by every
returned site, also after the relayout of the exterior wires. -/
theorem PreparationFrame.SelectedLookupSites.commonFrame
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence) (x : HeaderExterior wire header) (u : Fin (R+1)) :
    readings ((pub ∘ back) x u) 0=chosen.publication.frame :=
  (chosen.site (back x) u).origin

/-- Read a signed source packet on this family's actual published state.
The raw words, directory and header all come from the retained candidate. -/
theorem PreparationFrame.SelectedLookupSites.sharedCubeWords
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (signed : ∀ (x : X) u, ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      (chosen.site x u).old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word) (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (x : HeaderExterior wire header) (u : Fin (R+1)) :
    SharedCubeWords task decl F.group u.val (readings ((pub ∘ back) x u)) (F.source x u)
      (chosen.publication.directory.directory chosen.publication.privatePlacement chosen.publication.livePlacement).length :=
  chosen.projection.candidateSharedCubeWords G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase
    owner word pub mac reg mem host key sizes N cell label recv amount wire same chosen.site F signed valid axes space x u

end TeamContraction

end BorderVNP
end Computability
end OAI
