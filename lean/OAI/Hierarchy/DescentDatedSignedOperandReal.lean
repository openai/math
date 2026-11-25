import OAI.Hierarchy.DescentDatedSignedRealParent
import OAI.Hierarchy.DescentDatedOrdinaryPeer

namespace OAI
/-! Direct numerical operand of the physical signed resident, after the true
deduplicated halo selection and slot fetch. Both retained and split parents are covered. -/
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentOrdinarySignedRanks DescentOrdinarySignedMeta DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K A.cap≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K A.cap b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K A.cap)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)
local notation "group" => (Function.Embedding.refl (Fin groups))
local notation "home" => SignedExtent.wholeHost group host
local notation "name" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) (host.trans Fin.valEmbedding))

local instance : Fintype d₀.edge := d₀.finiteEdge
local instance : Fintype d₀.raw := d₀.finiteRaw
local instance : Fintype d₀.ticket := d₀.finiteTicket

local notation "RR" => Measured.roster d₀.blocks R symm d₀.observed
local notation "slot" h:arg e:arg => (RR).address h e
local notation "Z₀" => Incidence.of_measured d₀.blocks R symm d₀.observed d₀.order


open DescentPackedOperand DescentResetWindowFields
local notation "atChild" side:arg e:arg n:arg => Public.endpoint A native S ready name side (d₀.emission.units ⟨e,n⟩)

theorem real_operand (x : Fin (2^k)) (v : Fin H) (g : Fin groups) (h : Stage.Host (Fin groups) U k)
    (found : home x v g=some h) (edge : Local d₀.blocks h) (side : Bool)
    (here : (if side then d₀.blocks.dst edge.val else d₀.blocks.src edge.val)=h)
    (p : Fin (breadth degree)) (o : Fin O)
    (chosen : DescentHaloWalkRAM.Gather.select (DescentHaloWalkRAM.Gather.reaching R)
      (d₀.observed.venue h).1 p=some (d₀.observed.loc (d₀.observed.raw h edge)).1)
    (column : (d₀.observed.loc (d₀.observed.raw h edge)).2=o) (wireFit : A.cap≤2^b)
    (peerFit : A.degree≤2^b) {wordBits : ℕ} (wireWide : A.cap≤2^(wordBits+2))
    (peerWide : A.degree≤2^(wordBits+2)) (chunk grain : Cell (wordBits+2))
    (child : Fin (d₀.blocks.count edge.val)) (offset : d₀.core edge.val→chunk.val/grain.val=child.val) :
    let j:=finProdFinEquiv (p,o)
    let a:=atChild side edge.val child
    let tag:=decide (d₀.core edge.val)
    resolve (Public.fragment tag ((d₀.peer S ready x j v g).val:ℕ) ((d₀.serial S ready x j v g).val:ℕ) chunk grain)=
      .cable a.neighbor.val (a.wire.val-a.within.val) (if tag then chunk.val%grain.val else chunk.val) := by
  intro j a tag
  let first:Fin (d₀.blocks.count edge.val):=⟨0,edge.property.1⟩
  let face:=residentFace A native d₀.blocks h edge
  have atParent:=d₀.real_parent S ready x v g h found edge side face (residentFace_edge A native d₀.blocks h edge)
    p o chosen column wireFit peerFit
  have peer : (d₀.peer S ready x j v g).val=a.neighbor.val :=
    atParent.2.trans (congrArg Fin.val (resident_child_neighbor A native S ready name d₀.blocks d₀.core
      d₀.emission h edge child side here))
  have firstWire : (d₀.serial S ready x j v g).val=(atChild side edge.val first).wire.val := atParent.1
  have base:=DescentResetWindowFields.serial A native S ready name d₀.blocks d₀.core d₀.emission edge.val first side
  have step:=DescentResetWindowFields.serial A native S ready name d₀.blocks d₀.core d₀.emission edge.val child side
  have next : a.wire.val=(d₀.serial S ready x j v g).val+child.val := by
    rw [firstWire,base]
    simpa only [first,Nat.add_zero] using step
  have within:= (DescentResetWindowFields.metadata A native S ready name d₀.blocks d₀.core d₀.emission edge.val child side).1
  change a.within.val=(if d₀.core edge.val then 0 else child.val) at within
  have peerSmall : (d₀.peer S ready x j v g).val<2^(wordBits+2) := by
    rw [peer]
    exact a.neighbor.isLt.trans_le peerWide
  have wireSmall : (d₀.serial S ready x j v g).val<2^(wordBits+2) := by
    rw [firstWire]
    exact (atChild side edge.val first).wire.isLt.trans_le wireWide
  have storedPeer : (((d₀.peer S ready x j v g).val:ℕ):Cell (wordBits+2)).val=a.neighbor.val :=
    (Fin.val_cast_of_lt peerSmall).trans peer
  by_cases marked:d₀.core edge.val
  · have resolved:=(DescentDatedPublicGrain.resolve_public chunk ((d₀.peer S ready x j v g).val:ℕ)
        ((d₀.serial S ready x j v g).val:ℕ) grain).1
    simpa only [tag,decide_eq_true marked,ite_true,storedPeer,Fin.val_cast_of_lt wireSmall,
      next,within,ite_eq_left marked,Nat.sub_zero,offset marked] using resolved
  · have resolved:=(DescentDatedPublicGrain.resolve_public chunk ((d₀.peer S ready x j v g).val:ℕ)
        ((d₀.serial S ready x j v g).val:ℕ) grain).2
    simpa only [tag,decide_eq_false marked,Bool.false_eq_true,ite_false,storedPeer,Fin.val_cast_of_lt wireSmall,
      next,within,ite_eq_right marked,Nat.add_sub_cancel] using resolved

/-- Evaluating at the real child itself fixes the receiver, the duplicate-free
visit, and the earlier column. No independent lookup-address witness is needed. -/
theorem actual_operand (e : d₀.edge) (side : Bool) (child : Fin (d₀.blocks.count e))
    (wireFit : A.cap≤2^b) (peerFit : A.degree≤2^b) {wordBits : ℕ}
    (wireWide : A.cap≤2^(wordBits+2)) (peerWide : A.degree≤2^(wordBits+2))
    (chunk grain : Cell (wordBits+2)) (offset : d₀.core e→chunk.val/grain.val=child.val) :
    let h:=if side then d₀.blocks.dst e else d₀.blocks.src e
    let edge : Local d₀.blocks h:=⟨e,Nat.zero_lt_of_lt child.isLt,by cases side <;> simp [h]⟩
    let j:=(RR).address h edge
    let a:=atChild side e child
    let tag:=decide (d₀.core e)
    resolve (Public.fragment tag ((d₀.peer S ready h.2 j (host h.1.2) h.1.1).val:ℕ)
      ((d₀.serial S ready h.2 j (host h.1.2) h.1.1).val:ℕ) chunk grain)=
        .cable a.neighbor.val (a.wire.val-a.within.val) (if tag then chunk.val%grain.val else chunk.val) := by
  intro h edge j a tag
  have whereAt:= (SignedExtent.wholeHost_iff group host h.2 (host h.1.2) h.1.1 h).2 ⟨rfl,rfl,rfl⟩
  let idx:=Measured.visit d₀.blocks R symm d₀.observed h edge
  let col:=(d₀.observed.loc (d₀.observed.raw h edge)).2
  have read : Gather.select (Gather.reaching R) (d₀.observed.venue h).1 idx=
      some (d₀.observed.loc (d₀.observed.raw h edge)).1 :=
    Resident.visit_read d₀.blocks h (fun b=>(d₀.observed.venue b).1) d₀.observed.loc (d₀.observed.raw h)
      (Gather.reaching R) (Measured.near d₀.blocks R symm d₀.observed h) edge
  exact d₀.real_operand S ready h.2 (host h.1.2) h.1.1 h whereAt edge side rfl idx col read rfl
    wireFit peerFit wireWide peerWide chunk grain child offset

end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

end OAI
