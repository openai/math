import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # The single positive indicator on an observed Boolean pin -/

noncomputable section
namespace Hierarchy.Tagged.KeepBit
open ThreeFlat Routing
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

def network (F : Type*) [Zero F] [One F] (pin : V) : BitNetwork F (Fintype.card V) where
  cells := 1
  internal := 0
  source _ _ := .pin (Fintype.equivFin V pin)
  table _ x := if x 0=true then 1 else 0

theorem value (F : Type*) [CommSemiring F] (pin : V) (x : V→Bool) :
    TypedWiring.value (network F pin) x = if x pin=true then 1 else 0 := by
  simp only [TypedWiring.value,BitNetwork.eval,BitNetwork.weight,BitNetwork.factor,network,
    BitSource.read,Equiv.symm_apply_apply]
  change (∑ _ : Fin 0→Bool, ∏ _ : Fin 1, if x pin=true then (1:F) else 0) = _
  simp []

theorem cost (F : Type*) [Zero F] [One F] (pin : V) :
    (network F pin).cells+(network F pin).internal=1 := rfl
end Hierarchy.Tagged.KeepBit

end
end OAI
