import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentDonorSupplyRead

namespace OAI
/-! # Decode fixed old source seats into the eleven-role donor slab -/
namespace Hierarchy.DescentRawCablePanel
open DescentPackedZip DescentSIMDLookup DescentSixParty DescentSharedCableNames DescentHostDirectory
open DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k t : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)

theorem first_slot (q : DescentSharedCableNames.Stage.Positive A) :
    let h:=DescentSharedCableNames.Stage.home A (W.graph.src q.val)
    let id:=DescentSharedCableNames.Stage.signed A native S ready h.1 h.2 (Stage.originPort A q)
    id=(DescentSharedCableNames.Stage.outgoing A native S ready q).castLE (show A.cap≤2*A.cap by omega) := by
  intro h id
  apply Fin.ext
  let E:=DescentSharedCableNames.Stage.source A native
  let j:=DescentSharedCableNames.Stage.ofPort A native h (Stage.originPort A q)
  let f:=DescentSharedCableNames.Stage.firstAt A native h q rfl
  have same : j=f:=Subtype.ext rfl
  change (finProdFinEquiv ((0:Fin 2),E.position (DescentSharedCableNames.Stage.measured A native S ready) h j)).val=
    (E.position (DescentSharedCableNames.Stage.measured A native S ready) h f).val
  simp [same,finProdFinEquiv_apply_val]

theorem source_peer (rank : J×V↪ℕ) (q : DescentSharedCableNames.Stage.Positive A) :
    let h:=DescentSharedCableNames.Stage.home A (W.graph.src q.val)
    let n:=Stage.cableNames k rank
    let t:=(DescentSharedCableNames.Stage.outgoing A native S ready q).castLE (show A.cap≤2*A.cap by omega)
    (DescentSignedCableCodec.decode A.degree A.cap (DescentSignedCableCodec.encode
      (DescentSharedCableNames.Stage.signedPanel A native S ready n h t))).elim 0 (fun v=>v.neighbor.val+1)=
      (Stage.sourceHandle A native S ready rank q).neighbor.val+1 := by
  intro h n t
  have shown_:=Stage.origin_stored A native S ready rank q
  have address : DescentSharedCableNames.Stage.signed A native S ready h.1 h.2 (Stage.originPort A q)=t :=
    first_slot A native S ready q
  have slotRead : DescentSharedCableNames.Stage.signedPanel A native S ready n h t =
      some (Stage.sourceHandle A native S ready rank q) := by
    rw [←address]
    exact shown_
  rw [DescentSignedCableCodec.decode_encode,slotRead]
  rfl

end
end Hierarchy.DescentRawCablePanel

end OAI
