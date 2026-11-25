import OAI.Hierarchy.DescentOriginalArgumentPointer
import OAI.Hierarchy.DescentTerminalPointerOrigin
import OAI.Hierarchy.DescentTerminalOperandSlotNumber

namespace OAI
/-! # Original argument names in the terminal rectangle -/
namespace Hierarchy.DescentSixParty.Reached

open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentLocalPrivateNames
open DescentSharedCableNames DescentOperandStateBanks DescentCompiler DescentStageEdgeReceipt
open DescentTerminalPointerIssue DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (shape : WorldShape p R B) (hp : 0<p) (pin : P→ℕ)
    (v : W.graph.Site) {N A oldNodes oldArgs Pn : ℕ}
variable (nodes : Fintype.card ((shape.sites v).recipe hp).Node≤N) (args : ∀u,((shape.sites v).recipe hp).arity u≤A)
    (beforeNodes : Fintype.card ((shape.sites v).recipe hp).Node≤oldNodes) (beforeArgs : ∀u,((shape.sites v).recipe hp).arity u≤oldArgs)
    (exterior : Attached W.graph v≃Fin Pn) (freeze : ℕ→ℕ)
omit [Fintype P] in
theorem argument_slot_number (j : Slot ((shape.sites v).recipe hp)) :
    (number v j.1).val*oldArgs+j.2.val=((slot ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) beforeNodes beforeArgs) j).val :=
  rectangle_slot_number ((shape.sites v).recipe hp) (number v) beforeNodes beforeArgs j

/-- Decoding a reached argument uses the least occupied private address, the first
signed cable grain, and the archived public copy from the original port. -/
theorem argument_origin (t : CellInputs cap.placement.degree cap.placement.cap N A)
    (population : t.n=Fintype.card ((shape.sites v).recipe hp).Node) (widths : ∀u,t.arity (row ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) nodes u)=((shape.sites v).recipe hp).arity u)
    (physical : ∀s:Slot ((shape.sites v).recipe hp),t.pointer ((slot ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) nodes args) s)=argumentPointer cap B number shape hp pin oldArgs ⟨v,s.1⟩ s.2.val)
    (frozen : ∀z:Attached W.graph v,freeze (pin z.val)=(exterior z).val) :
    Origin W.graph v ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) nodes args (slot ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) beforeNodes beforeArgs)
      (DescentTerminalPortChart.rank cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount age)) (cap.vertex.trans Fin.valEmbedding))) v (exterior.toEmbedding.trans Fin.valEmbedding)) (exterior.toEmbedding.trans Fin.valEmbedding) (reindexed t freeze) :=by
  apply origin_fields (A:=cap.placement) (native:=(cap.order.trans Fin.valEmbedding)) (S:=S) (ready:=cap.valid) (names:=(DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount age)) (cap.vertex.trans Fin.valEmbedding))))
    (v:=v) (port:=(exterior.toEmbedding.trans Fin.valEmbedding)) (hp:=hp) (r:=((shape.sites v).recipe hp)) (birth:=((number v).toEmbedding.trans Fin.valEmbedding)) (nodes:=nodes) (arity:=args)
    (aliases:=(slot ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) beforeNodes beforeArgs)) (t:=t) (freeze:=freeze) (original:=fun z=>pin z.val) population widths
  · intro s h hit
    rw [physical s]
    exact argumentPointer_private cap B number shape hp pin oldArgs v s.1 s.2 (slot ((shape.sites v).recipe hp) ((number v).toEmbedding.trans Fin.valEmbedding) beforeNodes beforeArgs)
      (argument_slot_number B number shape hp v beforeNodes beforeArgs) h hit
  · intro s e j clip live
    dsimp only
    intro hit
    rw [physical s,argumentPointer_cable cap B number shape hp pin oldArgs v s.1 s.2 e j clip hit]
    rfl
  · intro s z j clip hit
    rw [physical s]
    exact argumentPointer_pin cap B number shape hp pin oldArgs v s.1 s.2 z j clip hit
  · intro z
    exact (earlier_count exterior z).trans (frozen z).symm

end
end Hierarchy.DescentSixParty.Reached

end OAI
