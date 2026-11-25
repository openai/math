import OAI.Hierarchy.TaggedWideLeafWorkspace

namespace OAI
/-! # Transporting the workspace contraction to the physical finite enumerations -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction
open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {T E H P : Type}
    [Fintype T] [Fintype E] [Fintype H] [Fintype P]
    (b : T → Board F) (cap : E → ℕ)
    (live : ∀ t, Edge (b t).counts → Fin (b t).width → Prop)

/-- The finite sum with the enumeration used by a given physical caller. -/
abbrev sumWith {A : Type*} (enum : Fintype A) (f : A → F) : F :=
  letI := enum
  ∑ a, f a

/-- The original physical contraction holds for arbitrary enumerations of
its input, label, private, history and output assignments. -/
theorem close_workspace_fintypes
    (φ : (∀ i, (b i).Slots) → PrivatePorts cap → (H → Bool) → (P → Bool) → F)
    (f : (Pin b cap H P → Bool) → F)
    (readout : ∀ z y h p, f (write b cap z y h p) =
      (∏ i, (b i).settings.close (z i)) *
        (if supported b live z then φ z y h p else 0))
    (input : Fintype (Pin b cap H P → Bool))
    (labels : Fintype (∀ t, (b t).Labels))
    (privatePorts : Fintype (PrivatePorts cap))
    (history : Fintype (H → Bool))
    (plane : Fintype (P → Bool)) :
    sumWith input f = sumWith labels (fun a =>
      if bounded b live a then
        sumWith privatePorts (fun y => sumWith history (fun h => sumWith plane (φ (placed b a) y h)))
      else 0) := by
  revert input labels privatePorts history plane
  let nativeInput : Fintype (Pin b cap H P → Bool) := inferInstance
  let nativeLabels : Fintype (∀ t, (b t).Labels) := inferInstance
  let nativePrivate : Fintype (PrivatePorts cap) := inferInstance
  let nativeHistory : Fintype (H → Bool) := inferInstance
  let nativePlane : Fintype (P → Bool) := inferInstance
  intro input labels privatePorts history plane
  have hi : input = nativeInput := Subsingleton.elim _ _
  have hl : labels = nativeLabels := Subsingleton.elim _ _
  have hv : privatePorts = nativePrivate := Subsingleton.elim _ _
  have hh : history = nativeHistory := Subsingleton.elim _ _
  have hp : plane = nativePlane := Subsingleton.elim _ _
  subst input
  subst labels
  subst privatePorts
  subst history
  subst plane
  exact close_workspace b cap live φ f readout

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
