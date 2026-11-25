import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite
import OAI.Computability.BorderVNP.DiagonalSignedSharedCubeReadback

/-! # The field operands at a candidate's actual returned writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally TeamContraction JointHeader
open PackedHistoryCircuit Packing Packing.Directory LocalRow Transmission Crossing

variable {w R X : ℕ} (task : SignedTaskArena.Layout) {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    (raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (raw.2 p j))
variable {owner : ℕ → Fin (R+1)} {group : Fin task.cube.header.d → Fin (R+1)}
    {frame receiving : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin task.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {dim : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network dim P bits} {cell : N.Site → Fin task.cube.cells}
    {recv : A → Fin task.cube.cells} {amount : A → ℕ}

set_option maxHeartbeats 1500000 in
/-- The candidate's own label run, field installer words and private report
pointers are read from the selected public writer at this exact exterior. -/
theorem CandidateSite.signed_witness_words
    (site : CandidateSite (X:=X) task.cube D pp lp raw owner decl group frame receiving
      pins fields f guess pub mac reg mem host key sizes N cell recv amount)
    (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ)
    (signed : site.old=routingExtension (task.extension pinned f.team subtotal old) D origin edges cells)
    (range : declarationInRange raw) (axes : task.cube.header.a=task.cube.n+1) (space : task.after.packed≤2^w)
    (descriptors : task.after.descriptors<2^w) (params : task.p.parameters<2^w) (src : ℕ → ℕ)
    (image : src=readings site.receipt.history.sharedInput) :
    let W := site.receipt.history
    SharedCubeWords task decl group f.team (readings pub) src (D.directory pp lp).length ∧
    NativeEntry task.cube frame site.control decl.1 R
      (powerHeaderImage task.cube f.dst (readings site.receipt.labeling.val.2.2))
      (readings site.published.val.2.2) (readings W.dataInput) ∧
    readings W.dataInput (frame+44)=task.after.descriptors ∧ readings W.dataInput (frame+81)=task.cube.stop ∧
      readings W.dataInput (frame+95)=task.p.parameters := by
  intro W
  have boot := site.input
  rw [signed] at boot
  have native := site.receipt.native_entry task site.placement f old origin edges cells pinned subtotal site.fresh
    site.gates site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw site.actual boot
  have words := site.receipt.report_input_words task f old origin edges cells pinned subtotal site.fresh site.gates
    site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw site.actual boot descriptors params
  rw [site.origin] at native words
  exact ⟨site.receipt.shared_cube_words task site.placement f old origin edges cells pinned subtotal site.fresh site.gates
      site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw site.actual boot range axes space image,
    native,words⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
