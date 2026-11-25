import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites

/-! # Reading the lookup selected by a candidate writer -/

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
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount

variable {G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
  pub mac reg mem host key sizes N cell label recv amount}

/-- Keep the site, its evidence and its calibrated writer from the same
candidate selection, on the wire chosen by that selection. -/
noncomputable def selectedLookupOfCandidateWriters
    (evidence : (x : X) → (u : Fin (R+1)) → atSite(x,u) → Prop)
    (result : ∃ site : (x : X) → (u : Fin (R+1)) → atSite(x,u),
      (∀ x u, evidence x u (site x u)) ∧
        ∃ (wire : WireLayout (R+1) r link) (same : wire.header = skeleton.header),
          let back := (HeaderExterior.changeLayout skeleton wire same header).symm
          ∃ F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back),
            PreparationFrame.WriterProjection G wire ar D pp lp owner decl grp frame header pin guess dst ib hb sb
              (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
              (fun x u => (site (back x) u).published) (fun x u => (site (back x) u).receipt.endReg)
              (fun x u => (site (back x) u).receipt.out) (fun x u => (site (back x) u).receipt.events)
              (fun x u => (site (back x) u).receipt.history) F) :=
  let site := result.choose
  let attained := result.choose_spec
  let allocated := attained.2
  let wire := allocated.choose
  let same := allocated.choose_spec.choose
  let writer := allocated.choose_spec.choose_spec
  let F := writer.choose
  PreparationFrame.SelectedLookupSites.mk (task:=task) (skeleton:=skeleton) (header:=header)
    (wire:=wire) (same:=same) (F:=F) (evidence:=evidence) (word:=word) (label:=label) site attained.1 writer.choose_spec

end TeamContraction

end BorderVNP
end Computability
end OAI
