import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites

/-! # The admitted frame and lookup publication selected by the signed sites -/

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


variable {α ξ : ℝ} {scale : ℕ}
local notation3 (prettyPrint := false) "siteAt(" x "," u ")" =>
  CandidateSite («X»:=TeamScales.exterior ξ r scale) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount

set_option maxRecDepth 7500 in
set_option maxHeartbeats 2600000 in
/-- The physically returned epoch and signed writer already give a lookup
publication before choosing any report continuation or an owned-row builder. -/
theorem signedSelectedLookupSites (len : header.length=skeleton.header)
    (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    (P₀ : (x : X) → (u : Fin (R+1)) → siteAt(x,u) → Prop) (perPin : ∀ x u, ∃ z, P₀ x u z)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count≤task.cube.header.header)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val skeleton w)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal≤TeamScales.literal α scale) (headRoom : (skeleton.header:ℝ)≤r*(scale:ℝ)^(24/25:ℝ))
    (valid : declarationInRange word) :
    ∃ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous := (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∃ F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous),
        Nonempty (F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner
          word pub mac reg mem host key sizes N cell label recv amount wire₀ h P₀) := by
  obtain ⟨z,paid,wire₀,h,F,proj⟩ := signed_selected_candidates G skeleton header len ar D pp lp pin guess dst ib hb sb
    frame receivingBase owner grp word pub mac reg mem fit host key sizes N cell recv amount P₀ perPin subRoom copied
    processors literal teams literalRoom headRoom valid
  exact ⟨wire₀,h,F,⟨⟨z,paid,proj⟩⟩⟩

set_option maxRecDepth 7500 in
set_option maxHeartbeats 2600000 in
/-- Select the admitted frame and its original site witnesses together.
The resulting lookup publication keeps the charged epoch and writer of
each selected positive pin on the chosen reference layout. -/
theorem signedAdmittedCandidate_lookupSites (len : header.length=skeleton.header)
    (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    (P₀ : (x : X) → (u : Fin (R+1)) → siteAt(x,u) → Prop) (perPin : ∀ x u, ∃ z, P₀ x u z)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count≤task.cube.header.header)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val skeleton w)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal≤TeamScales.literal α scale) (headRoom : (skeleton.header:ℝ)≤r*(scale:ℝ)^(24/25:ℝ))
    (fixed : Block (R+1)) (template : Frame) (S : SourceReports ar own)
    (signed : ∀ (x : X) (u : Fin (R+1)) (z : siteAt(x,u)), P₀ x u z →
      ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
        z.old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R (TeamScales.exterior ξ r scale) task.cube.header.blocks task.cube.b task.cube.K task.cube.h
      label recv amount word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (values : CubeConstants.valueBound task.id<2^w) (room : task.cube.ReplayRoom w frame) (copies : 1≤task.cube.K)
    (after : ∀ z : (x : X) → (u : Fin (R+1)) → siteAt(x,u), (∀ x u, P₀ x u (z x u)) →
      ∀ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous := (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∀ F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous),
        PreparationFrame.WriterProjection G wire₀ ar D pp lp owner decl grp frame header pin guess dst ib hb sb
          (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous) (fun x u => (z (previous x) u).epoch)
          (fun x u => (z (previous x) u).published) (fun x u => (z (previous x) u).receipt.endReg)
          (fun x u => (z (previous x) u).receipt.out) (fun x u => (z (previous x) u).receipt.events)
          (fun x u => (z (previous x) u).receipt.history) F → F.AfterOwned task fixed label recv amount template count S) :
    ∃ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous := (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∃ (F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous))
        (B : F.Builders fixed task.id own), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed task.id own template total B ∧
          Nonempty (F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner
            word pub mac reg mem host key sizes N cell label recv amount wire₀ h P₀) := by
  obtain ⟨wire₀,h,F,B,agree,observed,site,kept,proj⟩ := signedAdmittedCandidate G skeleton header task D pp lp
    pin guess dst ib hb sb frame receivingBase owner word pub mac reg mem host key sizes N cell label recv amount
    len fit P₀ perPin subRoom copied processors literal teams literalRoom headRoom fixed template S signed valid
    allowed axes space values room copies after
  exact ⟨wire₀,h,F,B,agree,observed,⟨⟨site,kept,proj⟩⟩⟩

set_option maxRecDepth 7500 in
set_option maxHeartbeats 2600000 in
/-- Keep the returned-ownership readback for the very sites that produced
the signed builder. The continuation and the retained observation are
evaluated on one selection before that builder is formed. -/
theorem signedAdmittedCandidate_withReadback (len : header.length=skeleton.header)
    (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    (P₀ : (x : X) → (u : Fin (R+1)) → siteAt(x,u) → Prop) (perPin : ∀ x u, ∃ z, P₀ x u z)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count≤task.cube.header.header)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val skeleton w)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal≤TeamScales.literal α scale) (headRoom : (skeleton.header:ℝ)≤r*(scale:ℝ)^(24/25:ℝ))
    (fixed : Block (R+1)) (template : Frame) (S : SourceReports ar own)
    (signed : ∀ (x : X) (u : Fin (R+1)) (z : siteAt(x,u)), P₀ x u z →
      ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
        z.old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R (TeamScales.exterior ξ r scale) task.cube.header.blocks task.cube.b task.cube.K task.cube.h
      label recv amount word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (values : CubeConstants.valueBound task.id<2^w) (room : task.cube.ReplayRoom w frame) (copies : 1≤task.cube.K)
    (K : ∀ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous :=  (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∀ F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous),
        F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
          pub mac reg mem host key sizes N cell label recv amount wire₀ h P₀ → Prop)
    (retained : ∀ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous :=  (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∀ (F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous))
        (z : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
          pub mac reg mem host key sizes N cell label recv amount wire₀ h P₀),
        F.AfterOwned task fixed label recv amount template count S ∧ K wire₀ h F z) :
    ∃ (wire₀ : WireLayout (R+1) r link) (h : wire₀.header=skeleton.header),
      let previous := (HeaderExterior.changeLayout skeleton wire₀ h header).symm
      ∃ (F : PreparationFrame G wire₀ ar decl header pin (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous))
        (B : F.Builders fixed task.id own), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed task.id own template total B ∧
          ∃ z : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner
            word pub mac reg mem host key sizes N cell label recv amount wire₀ h P₀, K wire₀ h F z := by
  obtain ⟨wire₀,h,F,⟨z⟩⟩ := signedSelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb
    frame receivingBase owner word pub mac reg mem host key sizes N cell label recv amount len fit P₀ perPin subRoom
    copied processors literal teams literalRoom headRoom valid
  obtain ⟨next,observed⟩ := retained wire₀ h F z
  obtain ⟨B,agree,seen⟩ := signedCandidateFrameBuilders G skeleton header task D pp lp pin guess dst ib hb sb frame
    receivingBase owner word pub mac reg mem host key sizes N cell label recv amount wire₀ h z.site F z.projection
    fixed template S (fun x u => signed x u (z.site x u) (z.attained x u)) valid allowed axes space values room copies next
  exact ⟨wire₀,h,F,B,agree,seen,z,observed⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
