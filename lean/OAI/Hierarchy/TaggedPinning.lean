import OAI.Hierarchy.TaggedPinMap
import OAI.Hierarchy.CatalystSubstitutionLocal

namespace OAI
/-! # Preserving the exposed catalyst gap under matching zero padding -/

noncomputable section
namespace Hierarchy.Catalyst.Pin
open ThreeFlat LinearAlgebra.SpectralBooks
open CatalystSubstitution
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p q : ℕ}

/-- All pinned or copied data lie at the common origin, giving a local
restriction of the error which costs no catalyst gap. -/
theorem gap_adapted (X : Approximation F k q) (wire : Fin q → Option (Fin p))
    (f : (Fin q → Bool) → F) {D : ℝ} (g : X.Gap f D) :
    (adapted X wire).Gap (f ∘ data wire) D := by
  intro P
  let v : (Port q X.width → Bool) → F := (X.error f).coeff
  let K := fun (z : Fin p → Bool) (y : Fin q → Bool) => if y=data wire z then (1:F) else 0
  let Y := adapted X wire
  have eval : (Y.error (f ∘ data wire)).coeff =
      localAction (Equiv.refl (Port p X.width)) K v := by
    funext x
    change Y.coeff x - ideal X.width (f ∘ data wire) x = _
    erw [coeff_adapted X wire x]
    have id : ideal X.width (f ∘ data wire) x = ideal X.width f (readFull X.width wire x) := by
      unfold ideal readFull
      rfl
    rw [id]
    simp [localAction,K,v,readFull,Approximation.error,ite_mul]
    rfl
  rcases g P with zero | h
  · left
    change v=0 at zero
    rw [eval,zero,localAction_zero]
    rfl
  · right
    let y := fun b : Wire X.width × Bool => sites (p:=p) X.width (.inr b)
    have price := price_move_localAction P (Equiv.refl (Port p X.width)) K v
      (sites X.width) (0 : EuclideanSpace ℝ (Fin k)) y (fun _ => rfl)
    change P.price (bitTensor ((Y.error (f∘data wire)).coeff)) (sites X.width) ≤ _
    rw [eval]
    have input : Sum.elim (fun _ : Fin q => (0 : EuclideanSpace ℝ (Fin k))) y =
        sites (p:=q) X.width := by funext i; cases i <;> rfl
    rw [input] at price
    have noTravel : (∑ l : Fin p,
        dist (sites X.width ((Equiv.refl (Port p X.width)) (.inl l))) 0) = 0 := by
      simp [sites]
    rw [noTravel,add_zero] at price
    exact price.trans h

end Hierarchy.Catalyst.Pin

namespace Hierarchy.Tagged
open Catalyst
open scoped Classical

variable {F : Type*} [Field F] {k h w W : ℕ}

theorem narrower (hw : w ≤ W) (X : Approximation F k (pins h W)) {D : ℝ}
    (g : X.Gap (coeff F h W) D) :
    ∃ Y : Approximation F k (pins h w), Y.width = X.width ∧ Y.size ≤ X.size ∧
      Y.Gap (coeff F h w) D := by
  refine ⟨Pin.adapted X (padPins h hw),rfl,Pin.size_adapted _ _ ?_,?_⟩
  · unfold pins
    gcongr
  · rw [← coeff_padded hw]
    exact Pin.gap_adapted _ _ _ g

end Hierarchy.Tagged

end
end OAI
