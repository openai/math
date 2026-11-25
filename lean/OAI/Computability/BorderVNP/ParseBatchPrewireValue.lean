import OAI.Computability.BorderVNP.ParseBatchPrewireBudget

/-! # Summation of the physical within-team variables before placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.Prewire

open VPVNP BooleanTranscript
open scoped BigOperators Classical

variable {X Y I W J A : Type} [Fintype X] [Fintype Y] [Fintype I] [Fintype W] [Fintype J]
    [CommSemiring A] {s : ℕ} (f : X → (Y ⊕ I) ⊕ Bool) (c : BooleanTranscript.Circuit (X ⊕ W) s)
    (weighted : J → W) (weight : J → Bool → A)

/-- Free public slots, private team links and clamps assign each original query bit. -/
def readInput (y : Y → Bool) (privateBits : I → Bool) (x : X) : Bool :=
  (f x).elim (Sum.elim y privateBits) id

/-- The rewired physical network sums each interior wire assignment exactly once.
Repeated uses in the old query refer to the same bit of that assignment. -/
theorem rewire_value (y : Y → Bool) :
    let c' := circuit (projection f) c
    let w' : J → I ⊕ W := fun j => Sum.inr (weighted j)
    (BooleanLayout.layout c' w').network.value
      ((BooleanLayout.layout c' w').tables (BooleanLayout.factor c' weight)) (fun i _ => y i) =
    ∑ h : I → Bool, (BooleanLayout.layout c weighted).network.value
      ((BooleanLayout.layout c weighted).tables (BooleanLayout.factor c weight))
      (fun i _ => readInput f y h i) := by
  dsimp only
  rw [BooleanLayout.value_eq]
  simp_rw [BooleanLayout.value_eq]
  let term (p : (I → Bool) × (W → Bool)) :=
    if c.eval (Sum.elim (readInput f y p.1) p.2) then ∏ j, weight j (p.2 (weighted j)) else 0
  trans ∑ p, term p
  · apply Finset.sum_equiv (Equiv.sumArrowEquivProdArrow I W Bool) (fun _ => by simp)
    intro z _
    rw [circuit_eval]
    have he : (fun i : X ⊕ W => (projection f i).elim (Sum.elim y z) id) =
        Sum.elim (readInput f y (z ∘ Sum.inl)) (z ∘ Sum.inr) := by
      funext i
      rcases i with x | w
      · rcases h : f x with yi | b
        · rcases yi with y' | p <;> simp [projection,readInput,h]
        · simp [projection,readInput,h]
      · rfl
    rw [he]
    rfl
  · rw [Fintype.sum_prod_type]

end ParseBatch.Prewire

end BorderVNP
end Computability
end OAI
