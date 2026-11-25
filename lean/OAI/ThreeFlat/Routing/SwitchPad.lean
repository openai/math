import OAI.ThreeFlat.Routing.SwitchPins
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Zero padding the payload width of a tagged permutation switch -/

noncomputable section
namespace ThreeFlat.Routing
open scoped Classical

/-- Narrow records occupy the low bits of a wide physical word. -/
def widenRecord {v : ℕ} (u : ℕ) (x : Fin v → Bool) (j : Fin u) : Bool :=
  if hj : j.val < v then x ⟨j.val,hj⟩ else false

theorem widenRecord_injective {v u : ℕ} (hv : v ≤ u) : Function.Injective (widenRecord (v := v) u) := by
  intro x y h
  funext j
  simpa [widenRecord,j.isLt] using congrFun h (Fin.castLE hv j)

/-- All address bits are preserved. Surplus input and output bits are fixed to false. -/
def narrowSwitchPin {m u : ℕ} (v : ℕ) : SwitchPin m u → Option (SwitchPin m v)
  | .inl p => some (.inl p)
  | .inr (s,i,j) => if h : j.val < v then some (.inr (s,i,⟨j.val,h⟩)) else none

def narrowSwitchNetwork {F : Type*} {m u : ℕ} (v : ℕ)
    (N : BitNetwork F (Fintype.card (SwitchPin m u))) : BitNetwork F (Fintype.card (SwitchPin m v)) :=
  N.restrictPins (fun j ↦ (narrowSwitchPin v ((Fintype.equivFin _).symm j)).map (Fintype.equivFin _))

@[simp] theorem narrowSwitchNetwork_cells {F : Type*} {m u : ℕ} (v : ℕ)
    (N : BitNetwork F (Fintype.card (SwitchPin m u))) : (narrowSwitchNetwork v N).cells = N.cells := rfl

@[simp] theorem narrowSwitchNetwork_internal {F : Type*} {m u : ℕ} (v : ℕ)
    (N : BitNetwork F (Fintype.card (SwitchPin m u))) : (narrowSwitchNetwork v N).internal = N.internal := rfl

theorem RealizesTaggedSwitch.narrow {F : Type*} [CommSemiring F] {m v u : ℕ}
    {N : BitNetwork F (Fintype.card (SwitchPin m u))} (hN : RealizesTaggedSwitch N) (hv : v ≤ u) :
    RealizesTaggedSwitch (narrowSwitchNetwork v N) := by
  intro a
  let wide : SwitchPin m u → Bool := fun z ↦ ((narrowSwitchPin v z).map a).getD false
  rw [narrowSwitchNetwork,BitNetwork.restrictPins_eval]
  rw [show (fun j ↦ (((narrowSwitchPin v ((Fintype.equivFin _).symm j)).map (Fintype.equivFin _)).map
      (a ∘ (Fintype.equivFin _).symm)).getD false) = wide ∘ (Fintype.equivFin _).symm by
    funext j
    cases h : narrowSwitchPin v ((Fintype.equivFin _).symm j) <;> simp [wide,Function.comp_def,h]]
  rw [hN wide]
  let tag := fun i ↦ addressEquiv m (fun j ↦ a (SwitchPin.tag i j))
  let x := fun i j ↦ a (SwitchPin.input i j)
  let y := fun i j ↦ a (SwitchPin.output i j)
  have hdata (s : Bool) (i : Fin (2^m)) (j : Fin u) :
      wide (.inr (s,i,j)) = widenRecord u (fun k ↦ a (.inr (s,i,k))) j := by
    by_cases hj : j.val < v <;> simp [widenRecord,wide,narrowSwitchPin,hj]
  simp only [SwitchPin.output,SwitchPin.input,hdata]
  change taggedSwitch F tag (fun i ↦ widenRecord u (x i)) (fun i ↦ widenRecord u (y i)) = taggedSwitch F tag x y
  have hh : Routed tag (fun i ↦ widenRecord u (x i)) (fun i ↦ widenRecord u (y i)) ↔ Routed tag x y := by
    simp only [Routed,(widenRecord_injective hv).eq_iff]
  simp only [taggedSwitch,hh]

end ThreeFlat.Routing

end
end OAI
