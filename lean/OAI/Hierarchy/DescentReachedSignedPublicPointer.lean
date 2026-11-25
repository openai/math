import OAI.Hierarchy.DescentDatedSignedOperandReal
import OAI.Hierarchy.DescentReachedArgumentPointer

namespace OAI
/-! A true signed parent field after the physical deduplicated visit is the
first-cable pointer of the final reached recipe, including source-first loops. -/
set_option quotPrecheck false
namespace Hierarchy.DescentResetWindowFields
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open scoped Classical

variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] {d k i : ℕ} {bits : P → ℕ}
  {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k ↪ ℕ)
local notation "B" => Stage.source A native
local notation "stream" => Stage.stream A native
local notation "terms" => Stage.measured A native S ready
local notation "live" => DescentPackedOperand.Public.endpoint A native S ready names
variable (C : Blocks (Stage.source A native) E) (marked : E → Prop)


variable (emit : Emission A native C marked)

omit [Fintype E] in
theorem first_signed_fields (e : E) (j : Fin (C.count e)) (side : Bool) :
    let t:=emit.units ⟨e,j⟩
    let start : Stage.Grain A:=⟨t.1,⟨0,Nat.zero_lt_of_lt t.2.isLt⟩⟩
    (live side t).neighbor=(live side start).neighbor ∧
    (live side t).wire.val-(live side t).within.val=(live side start).wire.val := by
  intro t start
  constructor
  · exact DescentPackedOperand.Public.endpoint_neighbor A native S ready names side t start rfl rfl
  · have first:=emit.first_of_edge e j
    change emit.units ⟨e,if marked e then j else ⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩=start at first
    rw [←first]
    change (live side (emit.units ⟨e,j⟩)).wire.val-(live side (emit.units ⟨e,j⟩)).within.val=_
    rw [serial A native S ready names C marked emit e j side,
      (metadata A native S ready names C marked emit e j side).1]
    by_cases active : marked e
    · rw [ite_eq_left active,ite_eq_left active,serial]
      omega
    · rw [ite_eq_right active,ite_eq_right active,serial]
      simp

end Hierarchy.DescentResetWindowFields

namespace Hierarchy.DescentSixParty.Reached
open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentLocalPrivateNames
open DescentSharedCableNames DescentOperandStateBanks DescentCompiler DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z degree wire hist p : ℕ}
    (cap : Reached W G q ε S k age z degree wire hist) (hp : 0<p)
local notation "A" => cap.placement
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "group" => Function.Embedding.refl (Fin (S.groupCount age))
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
  ((group).trans Fin.valEmbedding) (cap.vertex.trans Fin.valEmbedding))
local notation "endpoint" => DescentPackedOperand.Public.endpoint A native S cap.valid names

theorem firstCable_endpoint (v : W.graph.Site) (edge : Incident W.graph v) (chunk : ℕ)
    (fits : (chunk+1)*p≤W.graph.width edge.val) (live : 0<(A).grainCount edge.val) :
    let side:=decide (W.graph.src edge.val≠v)
    let first:=endpoint side ⟨edge.val,⟨0,live⟩⟩
    cap.firstCable hp v edge chunk fits=.cable first.neighbor.val first.wire.val chunk := by
  rcases edge with ⟨e,incident⟩
  by_cases source : W.graph.src e=v
  · subst v
    simp only [firstCable,DescentTerminalPortChart.first,ne_eq,not_true_eq_false,decide_false]
    rfl
  · have target := incident.resolve_left source
    subst v
    simp only [firstCable,DescentTerminalPortChart.first,dite_eq_right source,decide_eq_true source]
    rfl

/-- For a real emitted unit of the normalized stage, the low address of its
first grain is the numerical signed serial minus the within-cable offset. -/
theorem firstCable_emission {E : Type} [Fintype E] (C : DescentParallelBase.Blocks (Stage.source A native) E)
    (marked : E→Prop) (emit : DescentResetWindowFields.Emission A native C marked)
    (v : W.graph.Site) (edge : Incident W.graph v) (piece : ℕ) (fits : (piece+1)*p≤W.graph.width edge.val)
    (e : E) (j : Fin (C.count e)) (address : (emit.units ⟨e,j⟩).1=edge.val) :
    let side:=decide (W.graph.src edge.val≠v)
    let wing:=endpoint side (emit.units ⟨e,j⟩)
    cap.firstCable hp v edge piece fits=.cable wing.neighbor.val (wing.wire.val-wing.within.val) piece :=by
  intro side wing
  let t:=emit.units ⟨e,j⟩
  have live : 0<(A).grainCount edge.val :=by rw [←address];exact Nat.zero_lt_of_lt t.2.isLt
  have first : (⟨t.1,⟨0,Nat.zero_lt_of_lt t.2.isLt⟩⟩:Stage.Grain A)=⟨edge.val,⟨0,live⟩⟩ :=by
    apply Sigma.ext address
    exact (Fin.heq_ext_iff (congrArg (A).grainCount address)).2 rfl
  obtain ⟨peer,num⟩:=DescentResetWindowFields.first_signed_fields A native S cap.valid names C marked emit e j side
  rw [cap.firstCable_endpoint hp v edge piece fits live]
  change Pointer.cable (endpoint side ⟨edge.val,⟨0,live⟩⟩).neighbor.val
    (endpoint side ⟨edge.val,⟨0,live⟩⟩).wire.val piece=_
  change Pointer.cable (endpoint side ⟨edge.val,⟨0,live⟩⟩).neighbor.val
    (endpoint side ⟨edge.val,⟨0,live⟩⟩).wire.val piece=
    Pointer.cable (endpoint side t).neighbor.val ((endpoint side t).wire.val-(endpoint side t).within.val) piece
  rw [←first]
  congr 1
  · exact (congrArg Fin.val peer).symm
  · exact num.symm

open scoped Fin.CommRing
open DescentDatedAddressBook DescentParallelBase DescentPacking DescentPackedOperand DescentSIMDLookup
open DescentOrdinarySignedRanks DescentOrdinarySignedMeta DescentParallelBase.ParentFilter DescentHaloWalkRAM
variable {H prior degree₀ Q O K b : ℕ}
    {R : Fin prior→Fin degree₀→Option (Fin prior)} {symm : ∀u v j,R u j=some v→∃n,R v n=some u}
    {hostRoom : Fintype.card cap.V≤H} {pitch : ℕ} {room : Fused.capacity degree₀ Q K cap.placement.cap≤2^b}
local notation "host" => cap.vertex.trans (Fin.castLEEmb hostRoom)
variable {before : Fin (2^k)→Fin (breadth degree₀*O)→Fin H→Fin (S.groupCount age)→Option (Fused.Raw R Q K cap.placement.cap b)}
  {parent : Fin (2^k)→Fin O→Fin prior→Fin (S.groupCount age)→Option (ParentFilter.Source (breadth degree₀) Q K cap.placement.cap)}
  {marks : Fin (2^k)→Fin (breadth degree₀*O)→Fin H→Fin (S.groupCount age)→Cell 1}
  (draw : SignedDrawing cap.placement (cap.order.trans Fin.valEmbedding) R symm (cap.vertex.trans (Fin.castLEEmb hostRoom)) pitch room before parent marks)
local instance : Fintype draw.edge := draw.finiteEdge
local instance : Fintype draw.raw := draw.finiteRaw
local instance : Fintype draw.ticket := draw.finiteTicket
local notation "RR" => Measured.roster draw.blocks R symm draw.observed

theorem actual_firstCable {wordBits : ℕ} (v : W.graph.Site) (edge : Incident W.graph v)
    (e : draw.edge) (j : Fin (draw.blocks.count e))
    (survivor : (draw.emission.units ⟨e,j⟩).1=edge.val)
    (chunk grain : Cell (wordBits+2)) (offset : draw.core e → chunk.val/grain.val=j.val)
    (low : ℕ) (paid : (if draw.core e then chunk.val%grain.val else chunk.val)=low)
    (fits : (low+1)*p≤W.graph.width edge.val) (wireFit : (A).cap≤2^b) (peerFit : (A).degree≤2^b)
    (wireWide : (A).cap≤2^(wordBits+2)) (peerWide : (A).degree≤2^(wordBits+2)) :
    let side:=decide (W.graph.src edge.val≠v)
    let h:=if side then draw.blocks.dst e else draw.blocks.src e
    let entry : DescentParallelBase.Local draw.blocks h:=⟨e,Nat.zero_lt_of_lt j.isLt,by cases hs : side <;> simp [h,hs]⟩
    let row:=(RR).address h entry
    let outcome:=resolve (Public.fragment (b:=wordBits) (decide (draw.core e)) ((draw.peer S cap.valid h.2 row (host h.1.2) h.1.1).val:ℕ)
      ((draw.serial S cap.valid h.2 row (host h.1.2) h.1.1).val:ℕ) chunk grain)
    Pointer.ofKey 0 outcome=cap.firstCable hp v edge low fits := by
  intro side h entry row outcome
  let t:=draw.emission.units ⟨e,j⟩
  have lower:=draw.actual_operand S cap.valid e side j wireFit peerFit wireWide peerWide chunk grain offset
  change outcome=.cable (endpoint side t).neighbor.val ((endpoint side t).wire.val-(endpoint side t).within.val)
    (if decide (draw.core e) then chunk.val%grain.val else chunk.val) at lower
  rw [lower,cap.firstCable_emission hp draw.blocks draw.core draw.emission v edge low fits e j survivor]
  change Pointer.cable (endpoint side t).neighbor.val ((endpoint side t).wire.val-(endpoint side t).within.val)
    (if decide (draw.core e) then chunk.val%grain.val else chunk.val)=_
  simp only [decide_eq_true_eq,paid]
  rfl

end
end Hierarchy.DescentSixParty.Reached

end OAI
