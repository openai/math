import OAI.Computability.BorderVNP.DiagonalBootLookupInputs
import OAI.Computability.BorderVNP.DiagonalCandidateFrameBuilders

/-! # Signed lookup publication from the admitted physical site histories -/

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

/-- The signed publication carried by this selected family of candidate sites.
Its two native returns and its full writer history use these sites directly. -/
noncomputable abbrev PreparationFrame.WriterProjection.candidatePublication
    (site : ∀ (x : X) u, CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount)
    (F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back))
    (proj : PreparationFrame.WriterProjection G wire ar D pp lp owner decl grp frame header pin guess dst ib hb sb
      (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
      (fun x u => (site (back x) u).published) (fun x u => (site (back x) u).receipt.endReg) (fun x u => (site (back x) u).receipt.out)
      (fun x u => (site (back x) u).receipt.events) (fun x u => (site (back x) u).receipt.history) F) : F.LookupPublication task :=
  ⟨D,pp,lp,owner,grp,frame,guess,dst,ib,hb,sb,
    fun x u => (site (back x) u).epoch,fun x u => (site (back x) u).published,
    fun x u => (site (back x) u).receipt.endReg,fun x u => (site (back x) u).receipt.out,
    fun x u => (site (back x) u).receipt.events,fun x u => (site (back x) u).receipt.history,proj⟩

/-- The same signed writer which supplies the epoch and directory returns
also supplies the actual scanner, fixed constants and decoded pointer words
on every admitted exterior and reached team. -/
theorem PreparationFrame.WriterProjection.candidateSharedCubeWords
    (site : ∀ (x : X) u, CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount)
    (F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back))
    (proj : PreparationFrame.WriterProjection G wire ar D pp lp owner decl grp frame header pin guess dst ib hb sb
      (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
      (fun x u => (site (back x) u).published) (fun x u => (site (back x) u).receipt.endReg) (fun x u => (site (back x) u).receipt.out)
      (fun x u => (site (back x) u).receipt.events) (fun x u => (site (back x) u).receipt.history) F)
    (signed : ∀ (x : X) u, ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      (site x u).old=routingExtension (task.extension pinned u.val subtotal old) D origin edges cells)
    (valid : declarationInRange word)
    (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w) :
    ∀ (x : HeaderExterior wire header) (u : Fin (R+1)), SharedCubeWords task decl F.group u.val
      (readings ((pub ∘ back) x u)) (F.source x u) count := by
  intro x u
  let z := site (back x) u
  obtain ⟨old,origin,edges,cells,pinned,subtotal,installed⟩ := signed (back x) u
  have boot := z.input
  rw [show z.old=routingExtension (task.extension pinned (BF u).team subtotal old) D origin edges cells from installed] at boot
  rw [proj.groupNumber]
  exact z.receipt.shared_cube_words task z.placement (BF u) old origin edges cells pinned subtotal z.fresh z.gates
    z.outputs z.width z.off z.ell z.control z.profile z.claims z.pad word z.actual boot valid axes space (proj.image x u)

end TeamContraction

end BorderVNP
end Computability
end OAI
