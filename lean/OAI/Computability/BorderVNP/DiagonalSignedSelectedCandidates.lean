import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection
import OAI.Computability.BorderVNP.CubeRouteExteriorBootstrap

/-! # The all-exterior frame from the frozen profile of an eligible signed candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open BorderVNP.Cube Physical Tally JointHeader PackedHistoryCircuit LocalRow Crossing

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (len : header.length=skeleton.header)
    (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (group : Fin ar.header.d → Fin (R+1))
    (word : Broadcast ar.n ar.header.d ar.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)

local notation3 (prettyPrint := false) "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1))
  (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

include len in
/-- Assemble the inverse on an admitted broadcast before choosing any joint preparation. The
per-pin predicates retain the complete source geometry and literal words of the original
return. A zero-payload physical exterior supplies the calibration reference. -/
theorem signed_selected_candidates {α ξ : ℝ} {scale : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    {I : Type*} [Fintype I] (host : I → Fin ar.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {D₀ : ℕ} {P A : Type*} {bits : P → ℕ} (N : Network D₀ P bits) (cell : N.Site → Fin ar.cells)
    (recv : A → Fin ar.cells) (amount : A → ℕ)
    (P₀ : (x : X) → (u : Fin (R+1)) → SignedPrep.CandidateSite («X»:=TeamScales.exterior ξ r scale) ar D pp lp word owner decl group
      frame receivingBase (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u) (reg x u) (mem x u)
      host key sizes N cell recv amount → Prop)
    (perPin : ∀ (x : X) u, ∃ s, P₀ x u s)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count≤ar.header.header)
    (copied : ∀ x : X,ReturnedHeaders G pin x.val skeleton w)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal ≤ TeamScales.literal α scale) (headRoom : (skeleton.header:ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (valid : declarationInRange word) :
    ∃ site : ∀ (x : X) (u : Fin (R+1)), SignedPrep.CandidateSite («X»:=TeamScales.exterior ξ r scale) ar D pp lp word owner decl group
      frame receivingBase (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u) (reg x u) (mem x u)
      host key sizes N cell recv amount,
      (∀ x u,P₀ x u (site x u)) ∧
      ∃ (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header),
      let back := (HeaderExterior.changeLayout skeleton wire same header).symm
      let W := fun (x : HeaderExterior wire header) u => (site (back x) u).receipt
      ∃ F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back),
        PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
          (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
          (fun x u => (site (back x) u).published) (fun x u => (W x u).endReg)
          (fun x u => (W x u).out) (fun x u => (W x u).events) (fun x u => (W x u).history) F := by
  choose site physical using perPin
  let x₀ : X := ⟨JointHeader.exterior skeleton header len (fun _ _ _ => false),
    fun block => JointHeader.observed_exterior skeleton header len _ block⟩
  exact ⟨site,physical,signed_candidate_frame G skeleton header len ar D pp lp pin guess dst ib hb sb frame
    receivingBase owner group word pub mac reg mem fit host key sizes N cell recv amount site subRoom copied x₀
    processors literal teams literalRoom headRoom valid⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
