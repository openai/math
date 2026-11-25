import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.ThreeFlat.FlipPins
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Substitution with fixed Boolean data

A fixed pin becomes a literal in every incident table. Other pins can remain
live, and each old catalyst pair keeps both of its physical port addresses.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution

open Catalyst ThreeFlat LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical

variable {k p r : ℕ} {F : Type*} [Field F]

private def pinLabel (b : Fin k → ℕ) (g : Fin p → Fin r ⊕ Bool) :
    Port p b → Option (Port r b)
  | .inl i => (g i).elim (fun j => some (.inl j)) (fun _ => none)
  | .inr w => some (.inr w)

private def offset (b : Fin k → ℕ) (g : Fin p → Fin r ⊕ Bool) : Port p b → Bool
  | .inl i => (g i).elim (fun _ => false) id
  | .inr _ => false

/-- Original data pins can be supplied by a live data bit or a fixed literal. -/
abbrev fixData (X : Approximation F k p) (g : Fin p → Fin r ⊕ Bool) : Approximation F k r where
  width := X.width
  network := (X.network.flipPins (fun i => offset X.width g ((Fintype.equivFin _).symm i))).restrictPins
    (fun i => (pinLabel X.width g ((Fintype.equivFin _).symm i)).map (Fintype.equivFin _))

theorem fixData_coeff (X : Approximation F k p) (g : Fin p → Fin r ⊕ Bool)
    (x : Port r X.width → Bool) :
    (fixData X g).coeff x =
      X.coeff (Sum.elim (fun i => (g i).elim (fun j => x (.inl j)) id) (fun w => x (.inr w))) := by
  unfold fixData Approximation.coeff
  rw [BitNetwork.restrictPins_eval, BitNetwork.eval_flipPins]
  apply congrArg X.network.eval
  funext i
  cases h : (Fintype.equivFin (Port p X.width)).symm i with
  | inl j => cases hg : g j <;> simp [pinLabel, offset, hg]
  | inr w => simp [pinLabel, offset]

omit [Field F] in
theorem fixData_size (X : Approximation F k p) (g : Fin p → Fin r ⊕ Bool) :
    (fixData X g).size + p = X.size + r := by
  change X.network.cells + X.network.internal + Fintype.card (Port r X.width) + p =
    X.network.cells + X.network.internal + Fintype.card (Port p X.width) + r
  simp only [Port, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Every choice of the live bits gives one of the original pointwise tests. -/
theorem fixData_pointwise (X : Approximation F k p) (g : Fin p → Fin r ⊕ Bool)
    (f : (Fin p → Bool) → F) {D : ℝ} (hf : X.PointwiseGap f D) :
    (fixData X g).PointwiseGap (fun y => f (fun i => (g i).elim y id)) D := by
  intro P y
  let t : Fin p → Bool := fun i => (g i).elim y id
  let f' := fun z : Fin r → Bool => f (fun i => (g i).elim z id)
  have coeff (u : Wire X.width × Bool → Bool) :
      ((fixData X g).pinnedError f' y).coeff u = (X.pinnedError f t).coeff u := by
    change (fixData X g).coeff (Sum.elim y u) - ideal X.width f' (Sum.elim y u) =
      X.coeff (Sum.elim t u) - ideal X.width f (Sum.elim t u)
    exact congrArg₂ (· - ·) (fixData_coeff X g (Sum.elim y u)) rfl
  have same : (fixData X g).pinnedError f' y = X.pinnedError f t :=
    congrArg (fun c => (⟨fun _ => Bool, fun _ => inferInstance, c⟩ :
      Raw.{0} (Wire X.width × Bool) F)) (funext coeff)
  change ((fixData X g).pinnedError f' y).coeff = 0 ∨ _
  rw [same]
  exact hf P t

/-- Fully evaluate the exposed data at one specified word. -/
abbrev pinWord (X : Approximation F k p) (a : Fin p → Bool) : Approximation F k 0 :=
  fixData X (Sum.inr ∘ a)

theorem pinWord_coeff (X : Approximation F k p) (a : Fin p → Bool)
    (x : Port 0 X.width → Bool) :
    (pinWord X a).coeff x = X.coeff (Sum.elim a (x ∘ Sum.inr)) := by
  exact fixData_coeff X (Sum.inr ∘ a) x

theorem pinWord_error (X : Approximation F k p) (a : Fin p → Bool) (f : (Fin p → Bool) → F)
    (x : Port 0 X.width → Bool) :
    ((pinWord X a).error (fun _ => f a)).coeff x = (X.pinnedError f a).coeff (x ∘ Sum.inr) := by
  change (pinWord X a).coeff x - ideal X.width (fun _ : Fin 0 → Bool => f a) x =
    X.coeff (Sum.elim a (x ∘ Sum.inr)) - ideal X.width f (Sum.elim a (x ∘ Sum.inr))
  rw [pinWord_coeff]; rfl

private def fiberBool {Z : Type} (z : Fin 0 ⊕ Z) :
    Bool ≃ ({w : Z // (Sum.inr w : Fin 0 ⊕ Z) = z} → Bool) :=
  match z with
  | .inl i => i.elim0
  | .inr w => {
      toFun b _ := b
      invFun f := f ⟨w,rfl⟩
      left_inv _ := rfl
      right_inv f := by
        funext u
        exact congrArg f (Subtype.ext (Sum.inr.inj u.property).symm) }

private theorem pin_price (X : Approximation F k p) (a : Fin p → Bool) (f : (Fin p → Bool) → F)
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) :
    P.price ((pinWord X a).error (fun _ => f a)) (sites (p:=0) X.width) =
      P.price (X.pinnedError f a) (fun i => sites (p:=p) X.width (.inr i)) := by
  let U := X.pinnedError f a
  let T : Raw.{0} (Port 0 X.width) F := (pinWord X a).error (fun _ => f a)
  have same : (fun i => sites (p:=p) X.width (.inr i)) =
      sites (p:=0) X.width ∘ Sum.inr := by
    funext i
    rcases i with ⟨⟨j,t⟩,u⟩
    rfl
  rw [same, P.group]
  change P.price T (sites X.width) = P.price (U.group Sum.inr) (sites X.width)
  cases isEmpty_or_nonempty (Port 0 X.width) with
  | inl he =>
    have equal : sites (p:=0) X.width = fun _ => 0 := funext fun i => (he.false i).elim
    rw [equal, P.collapsed T, P.collapsed]
  | inr hn =>
    have eqv : T.Equivalent (U.group Sum.inr) :=
      Raw.reindex_equivalent (X:=T) (Y:=U.group Sum.inr) fiberBool (pinWord_error X a f)
    exact le_antisymm (P.placed_mono _ eqv.1) (P.placed_mono _ eqv.2)

/-- A pointwise gap becomes an ordinary exposed gap for the physically pinned
network. This applies to every word and also covers an empty catalyst. -/
theorem pinWord_gap (X : Approximation F k p) (a : Fin p → Bool)
    (f : (Fin p → Bool) → F) {D : ℝ} (h : X.PointwiseGap f D) :
    (pinWord X a).Gap (fun _ => f a) D := by
  intro P
  rcases h P a with hz | hp
  · left
    funext x
    exact (pinWord_error X a f x).trans (congrFun hz _)
  · right
    change P.price ((pinWord X a).error (fun _ => f a)) (sites (p:=0) X.width) ≤ _
    rw [pin_price]
    exact hp

/-- Uniform gaps of all the physically pinned networks reconstruct the
pointwise gap of the original contraction, with the same discount. -/
theorem pointwise_of_pinWord_gap (X : Approximation F k p) (f : (Fin p → Bool) → F)
    {D : ℝ} (h : ∀ a, (pinWord X a).Gap (fun _ => f a) D) : X.PointwiseGap f D := by
  intro P a
  rcases h a P with hz | hp
  · left
    funext w
    let x : Port 0 X.width → Bool := Sum.elim Fin.elim0 w
    exact (pinWord_error X a f x).symm.trans (congrFun hz x)
  · right
    rw [← pin_price]
    exact hp

end Hierarchy.CatalystSubstitution

end
end OAI
