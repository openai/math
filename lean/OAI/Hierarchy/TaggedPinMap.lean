import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Pinning matching zero padding on actual tagged networks -/

noncomputable section
namespace Hierarchy.Catalyst.Pin
open ThreeFlat LinearAlgebra.SpectralBooks
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p q : ℕ}

def data (wire : Fin q → Option (Fin p)) (x : Fin p → Bool) (j : Fin q) : Bool :=
  ((wire j).map x).getD false

def full (b : Fin k → ℕ) (wire : Fin q → Option (Fin p)) : Port q b → Option (Port p b)
  | .inl j => (wire j).map Sum.inl
  | .inr z => some (.inr z)

def adapted (X : Approximation F k q) (wire : Fin q → Option (Fin p)) : Approximation F k p where
  width := X.width
  network := X.network.restrictPins (fun i =>
    ((full X.width wire) ((Fintype.equivFin _).symm i)).map (Fintype.equivFin _))

def readFull (b : Fin k → ℕ) (wire : Fin q → Option (Fin p)) (x : Port p b → Bool) :
    Port q b → Bool := Sum.elim (data wire (x ∘ Sum.inl)) (x ∘ Sum.inr)

theorem coeff_adapted (X : Approximation F k q) (wire : Fin q → Option (Fin p))
    (x : Port p X.width → Bool) : (adapted X wire).coeff x = X.coeff (readFull X.width wire x) := by
  unfold adapted Approximation.coeff
  rw [BitNetwork.restrictPins_eval]
  apply congrArg X.network.eval
  funext i
  obtain ⟨j,rfl⟩ := (Fintype.equivFin (Port q X.width)).surjective i
  rcases j with a | b
  · cases h : wire a <;> simp [full,readFull,data,h]
  · simp [full,readFull]

omit [Field F] in
theorem size_adapted (X : Approximation F k q) (wire : Fin q → Option (Fin p)) (pq : p ≤ q) :
    (adapted X wire).size ≤ X.size := by
  change X.network.cells+X.network.internal+Fintype.card (Port p X.width) ≤
    X.network.cells+X.network.internal+Fintype.card (Port q X.width)
  apply Nat.add_le_add_left
  simp only [Port,Fintype.card_sum,Fintype.card_fin]
  exact Nat.add_le_add_right pq _

end Hierarchy.Catalyst.Pin

namespace Hierarchy.Tagged
open Catalyst
open scoped Classical

variable {F : Type*} [Field F] {k h w W : ℕ}

private def clip (_hw : w ≤ W) (j : Fin W) : Option (Fin w) :=
  if hj : j.val < w then some ⟨j.val,hj⟩ else none

def zeroExtend (hw : w ≤ W) : Bits w ↪ Bits W where
  toFun b j := ((clip hw j).map b).getD false
  inj' := by
    intro b c e
    funext j
    simpa [clip,j.isLt] using congrFun e (j.castLE hw)

def padPins (h : ℕ) (hw : w ≤ W) (i : Fin (pins h W)) : Option (Fin (pins h w)) :=
  match (portIndex h W).symm i with
  | .inl (r,j) => (clip hw j).map (fun s => portIndex h w (.inl (r,s)))
  | .inr (.inl r) => some (portIndex h w (.inr (.inl r)))
  | .inr (.inr (r,j)) => (clip hw j).map (fun s => portIndex h w (.inr (.inr (r,s))))

theorem coeff_padded (hw : w ≤ W) :
    coeff F h W ∘ Pin.data (padPins h hw) = coeff F h w := by
  funext x
  let z := Pin.data (padPins h hw) x
  have so : source z = zeroExtend hw ∘ source x := by
    funext i j
    change source z i j = ((clip hw j).map (source x i)).getD false
    cases eq : clip hw j <;> simp [z,source,Pin.data,padPins,eq]
  have ta : target z = zeroExtend hw ∘ target x := by
    funext i j
    change target z i j = ((clip hw j).map (target x i)).getD false
    cases eq : clip hw j <;> simp [z,target,Pin.data,padPins,eq]
  have tags : tag z = tag x := by
    funext i
    simp [z,tag,Pin.data,padPins]
  change (if Valid (source z) (tag z) (target z) then (1:F) else 0) = _
  rw [so,tags,ta,valid_map_iff]
  rfl

end Hierarchy.Tagged

end
end OAI
