import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWideStack
import OAI.Hierarchy.TaggedShorterBatchHost

namespace OAI
/-! # Installing the finite menu's physical compactors at the shared host pins -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ThreeFlat Routing Spill CallPool
open TaggedShorterCompaction TaggedShorterNetwork TaggedShorterGroups
open scoped Classical BigOperators
variable {F : Type*} {V : Type} [Field F] [Fintype V]

section
variable {S D M n w : ℕ}
    (near : Compactor F D (2^n) (n+w)) (far : Compactor F S M (Width (2^n) (n+w)))
    (readPin : Input S D (n+w) → V)

/-- Source, control and site bits are shared. Only the numbered homogeneous
tagged-product socket is private to this component. The compactors, their
capacity and every pin map are fixed before a selector is read. -/
def sharedCut : BitNetwork F (Fintype.card (V ⊕ Fin ((M*2)*pins n w))) :=
  WideHost.onPins (TaggedShorterBatchHost.cut near far).compactHidden (Sum.map readPin id)

theorem sharedCut_contract (v : V → Bool) :
    (∑ z,TypedWiring.value (sharedCut near far readPin) (Sum.elim v z) *
      CorrectionFrame.dataProduct (M*2) (coeff F n w) z) =
      TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
        (oracle F n w) (v ∘ readPin) := by
  rw [←TaggedShorterBatchHost.contract near far (v ∘ readPin)]
  apply Finset.sum_congr rfl
  intro z _
  rw [sharedCut,WideHost.onPins_value]
  congr 1
  have pinEq : (Sum.elim v z) ∘ (Sum.map readPin id) = Sum.elim (v ∘ readPin) z := by
    funext p
    cases p <;> rfl
  rw [pinEq]
  exact BitNetwork.compactHidden_eval _ _

theorem sharedCut_cost :
    (sharedCut near far readPin).cells+(sharedCut near far readPin).internal ≤
      4*(far.network.cells+2*S*near.network.cells+M*(lane F n n w).cells)+1 :=
  TaggedShorterBatchHost.size near far
end

/-- For the actual selected row list the same fixed cut now sees precisely
the occupied banks, endpoint masks and dense link IDs. -/
theorem sharedCut_linked (b : Board F) (v : V → Bool)
    (readPin : Input (capacity b.Group b.D b.halfBatch b.modules) b.D (b.address+b.width) → V)
    (payload : b.Slots)
    (settings : v ∘ readPin = input (read b.Group b.D b.halfBatch b.modules) payload
      b.settings.occupied b.settings.mask b.settings.id) :
    (∑ z, TypedWiring.value (sharedCut b.near b.far readPin) (Sum.elim v z) *
      CorrectionFrame.dataProduct (b.modules*2) (coeff F b.address b.width) z) =
        if ProtocolStackContraction.Linked b.place payload then 1 else 0 := by
  rw [sharedCut_contract,settings]
  exact b.checks.2 payload

end Hierarchy.Tagged.WideStack

end
end OAI
