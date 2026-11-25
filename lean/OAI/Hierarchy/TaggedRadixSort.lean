import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.ThreeFlat.Routing.SortNetwork

namespace OAI
/-! # A stable radix digit as a trivalent contraction

The tagged tensor's source array is addressed by tags on target rows. The
routing switch uses destination addresses on input rows. Wiring its output
array to the tagged source array gives a stable digit sort in either convention.
The wire map also transports the two binary address numberings explicitly.
-/

namespace Hierarchy.Tagged.Radix

open ThreeFlat
open Routing Routing.SortNetwork
open scoped Classical

noncomputable section

/-- Reindex a tagged source row by the destination-address convention. -/
def routeRow (h : ℕ) : Row h ≃ Row h := (Computability.VPVNP.RAMSerialization.wordBits h).trans (addressEquiv h)

def switchPort {h w : ℕ} : Port h w → SwitchPin h w
  | .inl (i,j) => SwitchPin.output (routeRow h i) j
  | .inr (.inl (i,j)) => SwitchPin.tag i j
  | .inr (.inr (i,j)) => SwitchPin.input i j

def switchIndex (h w : ℕ) (i : Fin (pins h w)) : Fin (Fintype.card (SwitchPin h w)) :=
  Fintype.equivFin _ (switchPort ((portIndex h w).symm i))

theorem coeff_switch {F : Type*} [Zero F] [One F] {h w : ℕ} (p : SwitchPin h w → Bool) :
    coeff F h w (fun i => p (switchPort ((portIndex h w).symm i))) =
      taggedSwitch F (fun i => addressEquiv h (fun j => p (SwitchPin.tag i j)))
        (fun i j => p (SwitchPin.input i j)) (fun i j => p (SwitchPin.output i j)) := by
  let t := fun i : Row h => (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun j => p (SwitchPin.tag i j))
  have tagEq (i : Row h) : routeRow h (t i) = addressEquiv h (fun j => p (SwitchPin.tag i j)) := by
    simp [routeRow, t]
  let x : Fin (pins h w) → Bool := fun i => p (switchPort ((portIndex h w).symm i))
  have src : source x = fun i j => p (SwitchPin.output (routeRow h i) j) := by
    funext i j
    simp only [Tagged.source, x, Equiv.symm_apply_apply, switchPort]
  have tgt : target x = fun i j => p (SwitchPin.input i j) := by
    funext i j
    simp only [Tagged.target, x, Equiv.symm_apply_apply, switchPort]
  have tagval : tag x = t := by
    funext i
    simp only [Tagged.tag, x, Equiv.symm_apply_apply, switchPort, t]
  unfold coeff taggedSwitch
  congr 1
  apply propext
  change Valid (source x) (tag x) (target x) ↔ _
  rw [src, tagval, tgt]
  unfold Valid Routed
  have eqtag : (fun i : Row h => addressEquiv h (fun j => p (SwitchPin.tag i j))) = routeRow h ∘ t :=
    funext fun i => (tagEq i).symm
  rw [eqtag, Equiv.comp_bijective]
  exact and_congr_right fun _ => forall_congr' fun _ => eq_comm

/-- One copy of the tagged test, with only its external pin names changed. -/
def switchOfTag {F : Type*} {h w : ℕ} (N : BitNetwork F (pins h w)) :
    BitNetwork F (Fintype.card (SwitchPin h w)) := N.restrictPins (some ∘ switchIndex h w)

theorem switchOfTag_realizes {F : Type*} [CommSemiring F] {h w : ℕ}
    (N : BitNetwork F (pins h w)) (exactN : ∀ x, N.eval x = coeff F h w x) :
    RealizesTaggedSwitch (switchOfTag N) := by
  intro p
  rw [switchOfTag, BitNetwork.restrictPins_eval, exactN]
  simpa only [Function.comp_apply, Option.map_some, Option.getD_some, switchIndex,
    Equiv.symm_apply_apply] using (coeff_switch (F := F) p)

/-- The continuation receives the uniquely and stably ordered records. -/
theorem stable_digit_eval {F : Type*} [CommSemiring F] {h w d : ℕ} (digit : Fin d → Fin w)
    (N : BitNetwork F (pins h (h+w))) (exactN : ∀ x, N.eval x = coeff F h (h+w) x)
    (T : BitNetwork F (Fintype.card (Payload h w))) (input : Records h w) :
    (sortThen digit (switchOfTag N) T).eval (pack input) =
      T.eval (pack (input ∘ Tuple.sort (fun i => addressEquiv d (input i ∘ digit)))) :=
  sortThen_eval digit _ (switchOfTag_realizes N exactN) T input

/-- Only the hidden sort guesses and the adjacent lexicographic checks add work. -/
theorem stable_digit_size {F : Type*} [Zero F] [One F] {h w d : ℕ} (digit : Fin d → Fin w)
    (N : BitNetwork F (pins h (h+w))) (T : BitNetwork F (Fintype.card (Payload h w))) :
    let R := sortThen digit (switchOfTag N) T
    R.cells + R.internal ≤ N.cells + N.internal + (T.cells + T.internal) +
      2^h*((h+h+w)+(h+d+1)+(h+d+2)*176) := by
  have c := sortThen_cells digit (switchOfTag N) T
  have i := sortThen_internal digit (switchOfTag N) T
  change _ ≤ N.cells + T.cells + _ at c
  change _ ≤ _ + N.internal + T.internal + _ at i
  dsimp only
  calc
    _ ≤ _ := Nat.add_le_add c i
    _ = _ := by ring

end
end Hierarchy.Tagged.Radix

end OAI
