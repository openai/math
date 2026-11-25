import OAI.Hierarchy.TaggedShorterBatchFormat
import OAI.Hierarchy.TaggedShorterNetwork
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # One numbered oracle occurrence for a complete positive-scale board -/

noncomputable section
namespace Hierarchy.TaggedShorterBatchHost
open ThreeFlat Routing Spill
open TaggedShorterCompaction TaggedShorterBatchFormat
open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {S D M n d w : ℕ}

abbrev Pins (S D M n d w : ℕ) := Input S D (d+w) ⊕ Fin ((M*2)*Tagged.pins n w)

def name (S D M n d w : ℕ) :
    TaggedShorterBank.OpenPins S D M (d+w) (TaggedShorterNetwork.Hole n w) ≃ Pins S D M n d w :=
  Equiv.sumCongr (Equiv.refl _) (pin M (Tagged.pins n w))

variable (near : Compactor F D (2^n) (d+w)) (far : Compactor F S M (Width (2^n) (d+w)))

def cut : BitNetwork F (Fintype.card (Pins S D M n d w)) :=
  (TaggedShorterBank.cut near far (TaggedShorterNetwork.lane F n d w)).restrictPins
    (some ∘ (Fintype.equivFin _) ∘ name S D M n d w ∘ (Fintype.equivFin _).symm)

theorem cut_eval (x : Input S D (d+w) → Bool) (z : Fin ((M*2)*Tagged.pins n w) → Bool) :
    TypedWiring.value (cut near far) (Sum.elim x z) =
      TypedWiring.value (TaggedShorterBank.cut near far (TaggedShorterNetwork.lane F n d w))
        (Sum.elim x (z ∘ pin M (Tagged.pins n w))) := by
  unfold cut TypedWiring.value
  rw [BitNetwork.restrictPins_eval]
  apply congrArg _
  funext j
  obtain ⟨p,rfl⟩ := (Fintype.equivFin _).surjective j
  cases p <;> simp [name,Function.comp_def]

/-- Even when the installed pool has many modules, substitution sees just
the one socket whose arity is the full homogeneous product. -/
theorem contract (x : Input S D (d+w) → Bool) :
    (∑ z, TypedWiring.value (cut near far) (Sum.elim x z) *
      CorrectionFrame.dataProduct (M*2) (Tagged.coeff F n w) z) =
      TaggedShorterBank.close (TaggedShorterBank.cut near far (TaggedShorterNetwork.lane F n d w))
        (TaggedShorterNetwork.oracle F n w) x := by
  let e := pin M (Tagged.pins n w)
  let E := e.arrowCongr (Equiv.refl Bool)
  let N := TaggedShorterBank.cut near far (TaggedShorterNetwork.lane F n d w)
  let named := fun z : Fin ((M*2)*Tagged.pins n w) → Bool =>
    TypedWiring.value (cut near far) (Sum.elim x z) *
      CorrectionFrame.dataProduct (M*2) (Tagged.coeff F n w) z
  let old := fun v : Fin M × TaggedShorterNetwork.Hole n w → Bool =>
    TypedWiring.value N (Sum.elim x v) * ∏ i, TaggedShorterNetwork.oracle F n w (fun p => v (i,p))
  have factor (v : Fin M × TaggedShorterNetwork.Hole n w → Bool) : old v = named (E v) := by
    dsimp only [old,named]
    rw [cut_eval,←product_eq]
    have pull : E v ∘ e = v := by
      funext i
      exact congrArg v (e.symm_apply_apply i)
    change _ = TypedWiring.value N (Sum.elim x (E v ∘ e)) * _
    rw [pull]
    apply congrArg (_ * ·)
    apply Finset.prod_congr rfl
    intro i _
    have atPin (b : Bool) (j : Fin (Tagged.pins n w)) : E v (e (i,b,j)) = v (i,b,j) :=
      congrFun pull (i,b,j)
    apply congrArg₂ (· * ·)
    · exact congrArg (Tagged.coeff F n w) (funext fun j => (atPin false j).symm)
    · exact congrArg (Tagged.coeff F n w) (funext fun j => (atPin true j).symm)
  have renumber := Fintype.sum_equiv E old named factor
  calc
    _ = ∑ z, named z := by
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext z
      simp
    _ = ∑ v, old v := renumber.symm
    _ = _ := by
      unfold TaggedShorterBank.close
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext v
      simp

theorem size :
    (cut near far).compactHidden.cells+(cut near far).compactHidden.internal ≤
      4*(far.network.cells+2*S*near.network.cells+
        M*(TaggedShorterNetwork.lane F n d w).cells)+1 := by
  simpa only [cut,BitNetwork.restrictPins,TaggedShorterBank.cut_cells] using
    BitNetwork.compactHidden_size (cut near far)

end Hierarchy.TaggedShorterBatchHost

end
end OAI
