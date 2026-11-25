import OAI.Hierarchy.ABPFirstCutCoeff
import OAI.Hierarchy.DegreeBorder

namespace OAI
/-! # Coordinate projections of a degree-component closure -/

namespace Hierarchy.ABPFirstCut

open MvPolynomial Computability.BorderVNP
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} [Fintype V] {F : Type*} [Field F]

omit [Fintype V] in
/-- Every term in the selected coefficient tensor has total degree equal to
its number of slots. -/
theorem degree_slotExponent (a : ∀ i, τ i) (S : Finset V) :
    (slotExponent a S).degree = S.card := by
  simp [slotExponent, Finsupp.degree_single]

/-- Selecting the squarefree, one-variable-per-slot coordinates sends the
closure of any degree-component model to the closure of its selected tensors. -/
theorem degreeModelClosure_readSlots {X : Type*} (readSlots : X → ∀ i, τ i)
    (model : ℕ → MvPolynomial (Σ i, τ i) F → Prop) {s : ℕ}
    (A : Set (X → F))
    (hexact : ∀ p, model s p → (fun x => slotCoeff (readSlots x) Finset.univ p) ∈ A)
    {p : MvPolynomial (Σ i, τ i) F}
    (hp : coeffVector (Fintype.card V) p ∈ degreeModelClosure model (Fintype.card V) s) :
    (fun x => slotCoeff (readSlots x) Finset.univ p) ∈ imageClosure A := by
  classical
  let idx (a : ∀ i, τ i) : DegreeMonomial (Σ i, τ i) (Fintype.card V) :=
    ⟨slotExponent a Finset.univ, by simp [degree_slotExponent]⟩
  have hmap := imageClosure_polynomial hp (fun a => MvPolynomial.X (idx (readSlots a)))
  simp only [eval_X] at hmap
  apply imageClosure_mono _ hmap
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  exact hexact q hq

/-- The ungrouped slot coefficient tensor is the identity case of the same projection. -/
theorem degreeModelClosure_slots
    (model : ℕ → MvPolynomial (Σ i, τ i) F → Prop) {s : ℕ}
    (A : Set ((∀ i, τ i) → F))
    (hexact : ∀ p, model s p → (fun a => slotCoeff a Finset.univ p) ∈ A)
    {p : MvPolynomial (Σ i, τ i) F}
    (hp : coeffVector (Fintype.card V) p ∈ degreeModelClosure model (Fintype.card V) s) :
    (fun a => slotCoeff a Finset.univ p) ∈ imageClosure A :=
  degreeModelClosure_readSlots id model A hexact hp

end
end Hierarchy.ABPFirstCut

end OAI
