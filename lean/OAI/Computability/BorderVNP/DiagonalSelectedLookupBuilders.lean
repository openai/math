import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrame

/-! # Scanning owners on an already selected publication -/

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

/-- The builders, their row agreement and their original owned traces all run
on the one frame retained by this publication. -/
theorem PreparationFrame.SelectedLookupSites.reportBuilders
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (fixed : Block (R+1)) (template : Frame) (S : SourceReports ar own)
    (signed : ∀ (x : X) u, ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      (chosen.site x u).old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R volume task.cube.header.blocks task.cube.b task.cube.K task.cube.h label recv amount word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (values : CubeConstants.valueBound task.id<2^w) (capacity : task.cube.ReplayRoom w frame)
    (copies : 1≤task.cube.K) (paid : F.AfterOwned task fixed label recv amount template count S) :
    ∃ B : F.Builders fixed task.id own, F.SourceAgreement fixed S B ∧
      F.ObservedBuilders fixed task.id own template total B :=
  signedCandidateFrameBuilders G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
    pub mac reg mem host key sizes N cell label recv amount wire same chosen.site F chosen.projection
    fixed template S signed valid allowed axes space values capacity copies paid

/-- Recover the exact calendar frame from its retained output, including its
preparation history and returned memory. -/
noncomputable abbrev PreparationFrame.SelectedLookupSites.installedFrame
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    := (fun _ : type_of% chosen => F) chosen

/-- Assemble the existential for one checked broadcast while retaining the
same site witnesses and reached reports after choosing the builders. -/
theorem PreparationFrame.SelectedLookupSites.admittedWithReports
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (fixed : Block (R+1)) (template : Frame) (S : SourceReports ar own)
    (signed : ∀ (x : X) u, ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      (chosen.site x u).old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R volume task.cube.header.blocks task.cube.b task.cube.K task.cube.h label recv amount word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (values : CubeConstants.valueBound task.id<2^w) (capacity : task.cube.ReplayRoom w frame)
    (copies : 1≤task.cube.K)
    (K : ∀ (l : WireLayout (R+1) r link) (h : l.header=skeleton.header),
      let before := (HeaderExterior.changeLayout skeleton l h header).symm
      ∀ A : PreparationFrame G l ar decl header pin (pub ∘ before) (mac ∘ before) (reg ∘ before) (mem ∘ before),
        A.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
          pub mac reg mem host key sizes N cell label recv amount l h evidence → Prop)
    (reached : K wire same F chosen) (paid : F.AfterOwned task fixed label recv amount template count S) :
    ∃ (l : WireLayout (R+1) r link) (h : l.header=skeleton.header),
      let before := (HeaderExterior.changeLayout skeleton l h header).symm
      ∃ (A : PreparationFrame G l ar decl header pin (pub ∘ before) (mac ∘ before) (reg ∘ before) (mem ∘ before))
        (B : A.Builders fixed task.id own), A.SourceAgreement fixed S B ∧ A.ObservedBuilders fixed task.id own template total B ∧
          ∃ z : A.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner
            word pub mac reg mem host key sizes N cell label recv amount l h evidence, K l h A z := by
  obtain ⟨B,agreement,observed⟩ := chosen.reportBuilders fixed template S signed valid allowed axes space values capacity copies paid
  exact ⟨wire,same,F,B,agreement,observed,chosen,reached⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
