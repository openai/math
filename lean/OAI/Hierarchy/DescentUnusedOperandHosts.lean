import OAI.Hierarchy.DescentScalarBookColumns
import OAI.Hierarchy.DescentPaidSweepTargetPadding

namespace OAI
/-! # A ghost host cannot acquire an operand from any old or newly printed value -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentPackedActorMask DescentPackedLocalAtoms DescentColonies
open DescentHaloWalkRAM DescentPackedColony DescentScalarVenueMask
open scoped Classical Fin.CommRing
noncomputable section
variable {D k K cap H G a nb mb : ℕ}

private theorem empty_grid (a n : ℕ) : encode a n (fun _=>0)=0:=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
  simp

theorem Values.book_no_hit (V : Values D k K cap H G a nb mb) (nodes) (h : Fin H) (g : Fin G)
    (miss : ∀j,V.venues h g j≠V.wanted h g) : V.book nodes h g=0:=by
  let d:=breadth D*2^k
  let r:=DescentPackedActorMask.actors d cap
  have flags : DescentPackedActorMask.target nb r (V.wanted h g) (encode nb r (V.venues h g))=encode 1 r (fun _=>0):=by
    unfold DescentPackedActorMask.target
    simp [miss]
  have noActors : occupied d K cap mb (encode 1 r (fun _=>0))
      (encode mb d (V.counts h g))=encode 1 (DescentPackedActorMask.nodes d K cap) (fun _=>0):=by
    unfold occupied
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    congr 1
    funext j
    obtain ⟨⟨p,q⟩,rfl⟩:=finProdFinEquiv.surjective j
    obtain ⟨s,rfl⟩:=finSumFinEquiv.surjective q
    cases s <;> simp [bitAt]
  have unused (raw : Cell (a * DescentPackedActorMask.nodes d K cap)) :
      DescentPackedLocalAtoms.pack a (DescentPackedActorMask.nodes d K cap) nodes
        (encode 1 _ (fun _ => 0)) raw = 0 := by
    unfold DescentPackedLocalAtoms.pack
    rw [Equiv.symm_apply_apply]
    refine Eq.trans ?_ (empty_grid a nodes)
    apply congrArg (encode a nodes)
    funext j
    simp [DescentPackedLocalAtoms.field]
  unfold Values.book
  rw [flags,noActors]
  exact unused _

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
