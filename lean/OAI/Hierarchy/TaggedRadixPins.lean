import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Tactic

namespace OAI
/-! # Constant and repeated pins of a physical tagged checker -/
noncomputable section
namespace Hierarchy.Tagged.RadixStage
open ThreeFlat Routing
open scoped Classical BigOperators
variable {F : Type*} {P : Type} [Fintype P]

private def sourceMap {P Q : Type} [Fintype P] [Fintype Q] (f : P → Q ⊕ Bool)
    (_ : Unit) (j : Fin (Fintype.card P)) : BitSource 0 (Fintype.card Q) :=
  (f ((Fintype.equivFin P).symm j)).elim (fun q => .pin (Fintype.equivFin Q q)) .constant

/-- Hardwired input bits, copies, and reindexings consume no cells. -/
def pullPins {Q : Type} [Fintype Q] (N : BitNetwork F (Fintype.card P)) (f : P → Q ⊕ Bool) :
    BitNetwork F (Fintype.card Q) := BitNetwork.glue (fun _ : Unit => N) (sourceMap f)

theorem pullPins_value [CommSemiring F] {Q : Type} [Fintype Q]
    (N : BitNetwork F (Fintype.card P)) (f : P → Q ⊕ Bool) (x : Q→Bool) :
    TypedWiring.value (pullPins N f) x = TypedWiring.value N (Sum.elim x id ∘ f) := by
  unfold pullPins TypedWiring.value
  rw [BitNetwork.glue_eval,Fintype.sum_unique,Fintype.prod_unique]
  apply congrArg N.eval
  funext i
  cases e : f ((Fintype.equivFin P).symm i) <;> simp [sourceMap,e,BitSource.read]

end Hierarchy.Tagged.RadixStage

end
end OAI
