import OAI.Computability.BorderVNP.DiagonalFrameReportBuilders
import OAI.Computability.BorderVNP.DiagonalSignedSelectedCandidates
import OAI.Computability.BorderVNP.DiagonalSignedCandidateCubeWords
import OAI.Computability.BorderVNP.DiagonalSharedDeclarationCapacity

/-! # The observed report builders for one admitted broadcast's actual writer frame -/

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


set_option maxHeartbeats 1800000 in
/-- The common-frame calibration and every required shared scanner word are
read from the selected candidate's own pinned history. The minimum follows
from its admitted broadcast. A single choice retains both the mathematical
row agreement and the actual scanner runs on every matching raw exterior. -/
theorem signedCandidateFrameBuilders
    (site : ∀ (x : X) u, CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount)
    (F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back))
    (proj : PreparationFrame.WriterProjection G wire ar D pp lp owner decl grp frame header pin guess dst ib hb sb
      (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
      (fun x u => (site (back x) u).published) (fun x u => (site (back x) u).receipt.endReg) (fun x u => (site (back x) u).receipt.out)
      (fun x u => (site (back x) u).receipt.events) (fun x u => (site (back x) u).receipt.history) F)
    (fixed : Block (R+1)) (template : Frame) (S : SourceReports ar own)
    (signed : ∀ (x : X) u, ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      (site x u).old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R volume task.cube.header.blocks task.cube.b task.cube.K task.cube.h label recv amount word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (values : CubeConstants.valueBound task.id<2^w) (room : task.cube.ReplayRoom w frame)
    (copies : 1≤task.cube.K) (afterOwned : F.AfterOwned task fixed label recv amount template count S) :
    ∃ B : F.Builders fixed task.id own, F.SourceAgreement fixed S B ∧
      F.ObservedBuilders fixed task.id own template total B := by
  have shared (x : HeaderExterior wire header) (u : Fin (R+1)) :
      SharedCubeWords task decl F.group u.val (readings ((pub ∘ back) x u)) (F.source x u) count := by
    let z := site (back x) u
    obtain ⟨old,origin,edges,cells,pinned,subtotal,installed⟩ := signed (back x) u
    have boot := z.input
    rw [show z.old=routingExtension (task.extension pinned (BF u).team subtotal old) D origin edges cells from installed] at boot
    rw [proj.groupNumber]
    exact z.receipt.shared_cube_words task z.placement (BF u) old origin edges cells pinned subtotal z.fresh z.gates
      z.outputs z.width z.off z.ell z.control z.profile z.claims z.pad word z.actual boot valid axes space (proj.image x u)
  have least : (decl).1=firstMinimum (fun j => ∑ pair,(decl).2 pair j) := by
    apply Fin.ext
    simpa only [Fin.ofNat,Fin.val_mk,Nat.mod_eq_of_lt valid.1,declaredMinimum] using allowed.1
  exact F.signedReportBuilders task fixed label recv amount template frame count S proj.shared proj.table
    (fun x u => (site (back x) u).origin) space values room shared proj.groupNumber least copies afterOwned

variable {α ξ : ℝ} {scale : ℕ}
local notation3 (prettyPrint := false) "siteAt(" x "," u ")" =>
  CandidateSite («X»:=TeamScales.exterior ξ r scale) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount

set_option maxHeartbeats 2600000 in
/-- From independently attained pin sites, select the common layout and
construct its observed signed builders for the admitted raw header. The
physical reports on that frame can refer to every site's retained evidence. -/
theorem signedAdmittedCandidate (len : header.length=skeleton.header)
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
          ∃ z : (x : X) → (u : Fin (R+1)) → siteAt(x,u), (∀ x u, P₀ x u (z x u)) ∧
            PreparationFrame.WriterProjection G wire₀ ar D pp lp owner decl grp frame header pin guess dst ib hb sb
              (pub ∘ previous) (mac ∘ previous) (reg ∘ previous) (mem ∘ previous) (fun x u => (z (previous x) u).epoch)
              (fun x u => (z (previous x) u).published) (fun x u => (z (previous x) u).receipt.endReg)
              (fun x u => (z (previous x) u).receipt.out) (fun x u => (z (previous x) u).receipt.events)
              (fun x u => (z (previous x) u).receipt.history) F := by
  obtain ⟨z,paid,wire₀,h,F,proj⟩ := signed_selected_candidates G skeleton header len ar D pp lp pin guess dst ib hb sb
    frame receivingBase owner grp word pub mac reg mem fit host key sizes N cell recv amount P₀ perPin subRoom copied
    processors literal teams literalRoom headRoom valid
  obtain ⟨B,source,observed⟩ := signedCandidateFrameBuilders G skeleton header task D pp lp pin guess dst ib hb sb frame
    receivingBase owner word pub mac reg mem host key sizes N cell label recv amount wire₀ h z F proj fixed template S
    (fun x u => signed x u (z x u) (paid x u)) valid allowed axes space values room copies (after z paid wire₀ h F proj)
  exact ⟨wire₀,h,F,B,source,observed,z,paid,proj⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
