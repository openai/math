import OAI.Hierarchy.TaggedRadixPins
import OAI.Hierarchy.TaggedRadixStages

namespace OAI
/-! # Pin the initial radix array and test the final array -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage
open ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} {P I O H : Type} [Fintype P] [Fintype I] [Fintype O] [Fintype H]

private def ends (I O H : Type) : Bool → Type
  | false => Pins I O H
  | true => O

private instance endFinite (b : Bool) : Fintype (ends I O H b) := by
  cases b
  · exact inferInstanceAs (Fintype (Pins I O H))
  · exact inferInstanceAs (Fintype O)

private def parts (N : Network F I O H) (C : BitNetwork F (Fintype.card O)) :
    (b : Bool) → BitNetwork F (Fintype.card (ends I O H b))
  | false => N
  | true => C

private def endWire (I O H : Type) : (b : Bool) → ends I O H b → (I ⊕ H) ⊕ O
  | false,.inl (.inl i) => .inl (.inl i)
  | false,.inl (.inr o) => .inr o
  | false,.inr h => .inl (.inr h)
  | true,o => .inr o

private def closeOutput (N : Network F I O H) (C : BitNetwork F (Fintype.card O)) :
    BitNetwork F (Fintype.card (I ⊕ H)) :=
  TypedWiring.glue (parts N C) (endWire I O H)

private theorem closeOutput_value [CommSemiring F] (N : Network F I O H)
    (C : BitNetwork F (Fintype.card O)) (x : I→Bool) (h : H→Bool) :
    TypedWiring.value (closeOutput N C) (Sum.elim x h) =
      ∑ y, row N x y h * TypedWiring.value C y := by
  unfold closeOutput
  rw [TypedWiring.glue_value]
  apply Finset.sum_congr rfl
  intro y _
  have l : (fun i : ends I O H false => Sum.elim (Sum.elim x h) y (endWire I O H false i)) =
      Sum.elim (Sum.elim x y) h := by
    funext i; rcases i with (i|i)|i <;> rfl
  have r : (fun i : ends I O H true => Sum.elim (Sum.elim x h) y (endWire I O H true i)) = y := rfl
  rw [Fintype.prod_bool,l,r]
  simp only [parts,row]
  exact mul_comm _ _

private def front (feed : I → P ⊕ Bool) : I ⊕ H → (P⊕H) ⊕ Bool
  | .inl i => (feed i).map Sum.inl id
  | .inr h => .inl (.inr h)

def «seal» (N : Network F I O H) (C : BitNetwork F (Fintype.card O)) (feed : I→P⊕Bool) :
    BitNetwork F (Fintype.card (P⊕H)) := pullPins (closeOutput N C) (front feed)

theorem seal_contract_on [CommSemiring F] (N : Network F I O H) (C : BitNetwork F (Fintype.card O))
    (feed : I→P⊕Bool) (φ : (H→Bool)→F) (f : (I→Bool)→(O→Bool)) (G : (I→Bool)→Prop) (ok : ComputesOn N φ G f)
    (x : P→Bool) (hx : G (Sum.elim x id ∘ feed)) :
    (∑ h,TypedWiring.value («seal» N C feed) (Sum.elim x h)*φ h) =
      TypedWiring.value C (f (Sum.elim x id ∘ feed)) := by
  let init := Sum.elim x id ∘ feed
  have pull (h : H→Bool) : (Sum.elim (Sum.elim x h) id ∘ front feed) = Sum.elim init h := by
    funext i
    rcases i with i|i
    · cases e : feed i <;> simp [Function.comp_def,init,front,e]
    · rfl
  simp_rw [«seal»,pullPins_value,pull,closeOutput_value,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ h,row N init y h * TypedWiring.value C y * φ h) =
        ∑ y,contract N φ init y * TypedWiring.value C y := by
          apply Finset.sum_congr rfl
          intro y _
          simp only [contract,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _
          ring
    _ = _ := by simp [ok init hx,ite_mul,init]

theorem seal_contract [CommSemiring F] (N : Network F I O H) (C : BitNetwork F (Fintype.card O))
    (feed : I→P⊕Bool) (φ : (H→Bool)→F) (f : (I→Bool)→(O→Bool)) (ok : Computes N φ f)
    (x : P→Bool) :
    (∑ h,TypedWiring.value («seal» N C feed) (Sum.elim x h)*φ h) =
      TypedWiring.value C (f (Sum.elim x id ∘ feed)) :=
  seal_contract_on N C feed φ f (fun _ => True) (fun y _ => ok y) x trivial

theorem seal_size (N : Network F I O H) (C : BitNetwork F (Fintype.card O))
    (feed : I→P⊕Bool) :
    («seal» N C feed).cells + («seal» N C feed).internal =
      N.cells+N.internal+C.cells+C.internal+Fintype.card O := by
  simp [«seal»,pullPins,closeOutput,parts]
 ; omega

end Hierarchy.Tagged.RadixStage

end
end OAI
