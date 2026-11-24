import OAI.Computability.VPVNP.BooleanTranscript
import OAI.Computability.VPVNP.ChoiceWitness
import OAI.Computability.VPVNP.PairedFamily

/-!
# The Boolean witness sum for the paired counting polynomial

The summand of §1.1 of *VP and VNP differ over every field* has visible variables
`(j,b)` and three sets of Boolean summation variables. They encode the input word,
the path choices, and the gate values of the deterministic verifier. Specialization
of the Boolean variables leaves a formal polynomial in the visible variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Verifier

open MvPolynomial
open BooleanTranscript (bit)

variable {n t g : ℕ} {R : Type*} [CommRing R]

/-- The verifier reads the word and the path choices. -/
abbrev Inputs (n t : ℕ) := Fin n ⊕ Fin t

/-- The summation also ranges over the claimed transcript of the verifier. -/
abbrev Witness (n t g : ℕ) := Inputs n t ⊕ Fin g

/-- Polynomial variables in the verifier summand, consisting of the paired input variables and
the Boolean witness coordinates. -/
abbrev Variables (n t g : ℕ) := (Fin n × Bool) ⊕ Witness n t g

/-- Multilinear selector for one pair of indeterminates. -/
def selector (x z₀ z₁ : R) : R := (1 - x) * z₀ + x * z₁

theorem selector_bit (b : Bool) (z₀ z₁ : R) :
    selector (bit b) z₀ z₁ = if b then z₁ else z₀ := by
  cases b <;> simp [selector, bit]

/-- Evaluate only the witness variables on the Boolean cube. -/
noncomputable def specialize {σ β : Type*} (w : β → Bool) :
    MvPolynomial (σ ⊕ β) R →+* MvPolynomial σ R :=
  eval₂Hom C (Sum.elim X (fun i => C (bit (w i))))

@[simp] theorem specialize_X_visible {σ β : Type*} (w : β → Bool) (z : σ) :
    specialize (R := R) w (X (Sum.inl z)) = X z := by simp [specialize]

@[simp] theorem specialize_X_witness {σ β : Type*} (w : β → Bool) (i : β) :
    specialize (R := R) (σ := σ) w (X (Sum.inr i)) = C (bit (w i)) := by simp [specialize]

/-- The verifier weight times the selectors, before any witness is fixed. -/
noncomputable def summand (c : BooleanTranscript.Circuit (Inputs n t) g) :
    MvPolynomial (Variables n t g) R :=
  c.weight (fun i => X (.inr (.inl i))) (fun i => X (.inr (.inr i))) *
    ∏ j : Fin n, selector (X (.inr (.inl (.inl j))))
      (X (.inl (j, false))) (X (.inl (j, true)))

private theorem C_bit (b : Bool) : C (σ := Fin n × Bool) (bit b : R) = bit b := by
  cases b <;> simp [bit]

/-- On fixing the witness, each selector becomes the single variable named by the input bit. -/
theorem specialize_summand (c : BooleanTranscript.Circuit (Inputs n t) g)
    (u : Inputs n t → Bool) (a : Fin g → Bool) :
    specialize (R := R) (Sum.elim u a) (summand c) =
      c.weight (bit ∘ u) (bit ∘ a) * ∏ j : Fin n, X (j, u (.inl j)) := by
  classical
  rw [summand, map_mul, c.weight_hom, map_prod]
  congr 1
  · congr 1 <;> funext i <;> simp [C_bit]
  · apply Finset.prod_congr rfl
    intro j _
    simp only [selector, map_add, map_mul, map_sub, map_one, specialize_X_witness,
      specialize_X_visible, Sum.elim_inl, C_bit]
    cases u (.inl j) <;> simp [bit]

private theorem sum_split {α β A : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [AddCommMonoid A]
    (f : (α ⊕ β → Bool) → A) :
    ∑ w, f w = ∑ x : α → Bool, ∑ y : β → Bool, f (Sum.elim x y) := by
  rw [← (Equiv.sumArrowEquivProdArrow α β Bool).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Eliminate the auxiliary transcript bits to obtain the coefficient-counting polynomial. -/
theorem sum_summand (c : BooleanTranscript.Circuit (Inputs n t) g) :
    ∑ w : Witness n t g → Bool, specialize (R := R) w (summand c) =
      pairedPolynomial (fun x => ∑ y : Fin t → Bool, bit (c.eval (Sum.elim x y))) := by
  classical
  rw [sum_split, sum_split, pairedPolynomial]
  apply Finset.sum_congr rfl
  intro x _
  simp only [specialize_summand, Sum.elim_inl, ← Finset.sum_mul, c.sum_weight_bits]
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact (C_bit _).symm

/-- The §1.1 summand computes the actual integer family after base change whenever its
Boolean circuit implements the canonical path verifier. This separates the exact counting
identity from the problem of constructing a polynomial-size circuit for that verifier. -/
theorem sum_summand_eq_map_P
    (c : BooleanTranscript.Circuit (Inputs n (n ^ clockExponent)) g)
    (hc : ∀ x y, c.eval (Sum.elim x y) = verifiesInput x y) :
    ∑ w : Witness n (n ^ clockExponent) g → Bool, specialize (R := R) w (summand c) =
      MvPolynomial.map (Int.castRingHom R) (P n) := by
  rw [sum_summand, map_P]
  congr 1
  funext x
  simpa only [hc, bit] using (acceptingCount_eq_sum_witnesses (R := R) x).symm

end Verifier

end VPVNP
end Computability
end OAI
