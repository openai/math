import OAI.Hierarchy.DescentDatedSignedOperandReal
import OAI.Hierarchy.DescentDatedSignedNumbers

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentOrdinarySignedRanks DescentOrdinarySignedMeta DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K L b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K L≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K L b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K L)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)
local notation "group" => (Function.Embedding.refl (Fin groups))
local notation "home" => SignedExtent.wholeHost group host
local notation "name" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) (host.trans Fin.valEmbedding))

local instance capacityEdgeFintype : Fintype d₀.edge := d₀.finiteEdge
local instance capacityRawFintype : Fintype d₀.raw := d₀.finiteRaw
local instance capacityTicketFintype : Fintype d₀.ticket := d₀.finiteTicket

local notation "RR" => Measured.roster d₀.blocks R symm d₀.observed
local notation "slot" h:arg e:arg => (RR).address h e
local notation "Z₀" => Incidence.of_measured d₀.blocks R symm d₀.observed d₀.order


open DescentPackedOperand DescentResetWindowFields
local notation "atChild" side:arg e:arg n:arg => Public.endpoint A native S ready name side (d₀.emission.units ⟨e,n⟩)

theorem budgeted_operand (capacity : A.cap=L) (e : d₀.edge) (side : Bool) (child : Fin (d₀.blocks.count e))
    (wireFit : A.cap≤2^b) (peerFit : A.degree≤2^b) {wordBits : ℕ}
    (wireWide : A.cap≤2^(wordBits+2)) (peerWide : A.degree≤2^(wordBits+2))
    (chunk grain : Cell (wordBits+2)) (offset : d₀.core e→chunk.val/grain.val=child.val) :
    let h:=if side then d₀.blocks.dst e else d₀.blocks.src e
    let edge : Local d₀.blocks h:=⟨e,Nat.zero_lt_of_lt child.isLt,by cases side <;> simp [h]⟩
    let j:=(RR).address h edge
    let a:=atChild side e child
    let tag:=decide (d₀.core e)
    resolve (Public.fragment tag (d₀.digits S ready capacity h.2 j (host h.1.2) h.1.1).1
      (d₀.digits S ready capacity h.2 j (host h.1.2) h.1.1).2 chunk grain)=
        .cable a.neighbor.val (a.wire.val-a.within.val) (if tag then chunk.val%grain.val else chunk.val) :=by
  subst L
  exact d₀.actual_operand S ready e side child wireFit peerFit wireWide peerWide chunk grain offset

end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

end OAI
