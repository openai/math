import OAI.Hierarchy.DescentDatedSampledOldStamp
import OAI.Hierarchy.DescentDatedOriginalStampPage

namespace OAI
/-! # Reading the reached origin stamp at the padded physical host -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
noncomputable section

/-- Interpret the reached donor rows on the static dimensions of the physical return. -/
def Values.originTransport {D k K cap Q J r H a nb mb D' k' K' cap' Q' J' r' a' : ℕ}
    (degree:D'=D) (depth:k'=k) (oldNodes:K'=K) (capacity:cap'=cap)
    (lo:Q'=Q) (groups:J'=J) (radix:r'=r) (field:a'=a)
    (small:Fin Q→Values D k K cap H (J*r) a nb mb) :
    Fin Q'→Values D' k' K' cap' H (J'*r') a' nb mb :=by
  subst D'; subst k'; subst K'; subst cap'
  subst Q'; subst J'; subst r'; subst a'
  exact small

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentOrdinaryRasterReturn DescentSIMDLookup DescentHaloWalkRAM
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open DescentPackedActorMask
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin:Type} [Field F] (v:PhysicalOrdinary F Pin) (shape:v.VectorShape)
    {D k K cap Q J r H a a' nb mb:ℕ} (large:v.OriginalDonors a' nb mb)
    (wide:H≤v.vector.hosts) (small:Fin Q→Values D k K cap H (J*r) a nb mb)
    (degree:v.reference.degree=D) (depth:v.reference.k=k)
    (oldNodes:v.reference.oldNodes=K) (capacity:v.reference.capacity=cap)
    (lo:v.vector.lows=Q) (gs:v.vector.groups=J) (rad:v.vector.radix=r) (field:a'=a)
local notation "smallRows" => Values.originTransport degree depth oldNodes capacity lo gs rad field small
local notation "chart₁" => (⟨D,k,K,cap,v.resolver.nodes,v.originBits,H,Q,J,r,0⟩:Return)
local notation "count₁" => nodes (breadth D*2^k) K cap

private theorem tuple_host_lanes (layout : Return) (hosts lanes : ℕ) (i : Fin (extent layout)) :
    tuple layout i = tuple { layout with hosts, lanes } i := by
  cases h : finSumFinEquiv.symm (DescentOrdinaryAtomFieldRAM.bookItem layout.degree layout.depth
    layout.oldNodes layout.capacity i) <;> simp only [tuple, h]

private theorem readLaw_host_lanes (layout : Return) (hosts lanes bits : ℕ)
    (j : Fin layout.newNodes) (f : Fin 6) (w : Cell (layout.ordinalBits * layout.newNodes)) :
    readLaw layout bits j f w = readLaw { layout with hosts, lanes } bits j f w := by
  dsimp only [readLaw, extent]
  split
  · rw [tuple_host_lanes layout hosts lanes]
  · rfl

/-- The immutable field number selects the actor tag, sorted old-donor ordinal,
block or node from the same registered one-based stamp as the real output row. -/
theorem old_origin_digit (resident:∀l,Values.Prefix wide (smallRows l) (large l))
    (block:Fin r) (node:Fin v.resolver.nodes) (arg:Fin v.resolver.operands)
    (home:Fin (H*Q)) (group_:Fin J) (walk:Fin (breadth D)) (oldBlock:Fin (2^k)) (oldNode:Fin K)
    (stamp:((encode v.originBits v.resolver.nodes).symm
      (DescentScalarBookReshape.book
        (fun l h g=>selection count₁ v.resolver.nodes v.originBits (marked (small l) h g))
        block home group_) node).val=(candidate chart₁ walk oldBlock (.inl oldNode)).val+1)
    (f:Fin 6) (digitFit:(![1,walk.val,oldBlock.val,oldNode.val,0,0] f)<2^v.operandShortBits) :
    let job:=v.resolver.index ((block.cast rad.symm).cast shape.blocks.symm,node,arg)
    (v.originHeaderValue shape large job f
      ((widen wide (home.cast (congrArg (H*·) lo.symm))).cast shape.hosts.symm)
      ((group_.cast gs.symm).cast shape.groups.symm)).val =
        ![1,walk.val,oldBlock.val,oldNode.val,0,0] f :=by
  subst D; subst k; subst K; subst cap
  subst Q; subst J; subst r; subst a
  intro job
  let source:=DescentScalarBookReshape.book
    (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits (marked (small l) h g))
      block home group_
  have dims:v.resolver.index.symm job=(block.cast shape.blocks.symm,node,arg):=v.resolver.index.symm_apply_apply _
  have measured:=v.registered_origin_at shape large wide small resident job home (group_.cast shape.groups.symm) f
  have word:(v.originHeaderValue shape large job f ((widen wide home).cast shape.hosts.symm)
      (group_.cast shape.groups.symm)).val=(readLaw v.originChart v.operandShortBits node f source).val:=by
    apply (congrArg Fin.val measured).trans
    rw [dims]
    rfl
  have live:((encode v.originBits v.resolver.nodes).symm source node).val=
      (candidate v.originChart walk oldBlock (.inl oldNode)).val+1:=stamp
  exact word.trans (DescentDatedOperandReadPipeline.old_stamp_origin_values v.originChart v.operandShortBits
    walk oldBlock oldNode node source live f digitFit)

/-- The whole six-field response to a chronological old or newborn stamp, in the same
physical origin bank at the actual widened host and group. -/
theorem registered_origin_words (resident:∀l,Values.Prefix wide (smallRows l) (large l))
    (block:Fin r) (node:Fin v.resolver.nodes) (arg:Fin v.resolver.operands)
    (home:Fin (H*Q)) (group_:Fin J) :
    let job:=v.resolver.index ((block.cast rad.symm).cast shape.blocks.symm,node,arg)
    let word:=DescentScalarBookReshape.book
      (fun l h g=>selection count₁ v.resolver.nodes v.originBits (marked (small l) h g)) block home group_
    ∀f,v.originHeaderValue shape large job f ((widen wide (home.cast (congrArg (H*·) lo.symm))).cast shape.hosts.symm)
       ((group_.cast gs.symm).cast shape.groups.symm)=readLaw chart₁ v.operandShortBits node f word :=by
  subst D; subst k; subst K; subst cap
  subst Q; subst J; subst r; subst a
  intro job word f
  have pos:v.resolver.index.symm job=(block.cast shape.blocks.symm,node,arg):=v.resolver.index.symm_apply_apply _
  have measured:=v.registered_origin_at shape large wide small resident job home (group_.cast shape.groups.symm) f
  apply measured.trans
  rw [pos]
  exact readLaw_host_lanes v.originChart H 0 v.operandShortBits node f word

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
