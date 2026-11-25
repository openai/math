import OAI.LinearAlgebra.SpectralBooks.WordPermutations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators

/-! # Grouping contraction assignments by a fixed profile

The copies of each summand occupy one block. Within that block they appear in the order of
their positions in the word. This gives the same assignment type for all words of a fixed
profile while retaining the original position for each local table.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace WordsOfContent

variable {A : Type*} [DecidableEq A] {j : ℕ} {π : A → ℕ}

/-- The positions bearing letter `a`, enumerated in increasing order. -/
def occurrence (w : WordsOfContent (Fin j) A π) (a : A) :
    Fin (π a) ≃o {i : Fin j // w.1 i = a} :=
  Fintype.orderIsoFinOfCardEq _ (w.2 a)

/-- Reorder assignments within a word into a block for each summand. -/
def assignmentEquiv (w : WordsOfContent (Fin j) A π) (S : A → Type*) :
    ((i : Fin j) → S (w.1 i)) ≃ ((a : A) → Fin (π a) → S a) :=
  Equiv.piCongrFiberwise (f := w.1) fun a ↦
    (Equiv.piCongrRight fun i : {i : Fin j // w.1 i = a} ↦ Equiv.cast (congrArg S i.2)).trans
      (Equiv.arrowCongr (w.occurrence a).toEquiv.symm (Equiv.refl _))

/-- The `k`-th entry of a block is the assignment at the `k`-th occurrence of its letter. -/
theorem assignmentEquiv_apply (w : WordsOfContent (Fin j) A π) (S : A → Type*)
    (v : (i : Fin j) → S (w.1 i)) (a : A) (k : Fin (π a)) :
    w.assignmentEquiv S v a k =
      cast (congrArg S (w.occurrence a k).2) (v (w.occurrence a k).1) := rfl

/-- A word and its ordered assignments, with all assignment blocks now independent of the word. -/
def profileAssignmentEquiv (π : A → ℕ) (j : ℕ) (S : A → Type*) :
    (Σ w : WordsOfContent (Fin j) A π, (i : Fin j) → S (w.1 i)) ≃
      WordsOfContent (Fin j) A π × ((a : A) → Fin (π a) → S a) :=
  (Equiv.sigmaCongrRight (fun w ↦ assignmentEquiv w S)).trans (Equiv.sigmaEquivProd _ _)

variable {R : Type*}

private theorem prod_occurrences [Fintype A] [CommMonoid R]
    (w : WordsOfContent (Fin j) A π) (f : Fin j → R) :
    ∏ i, f i = ∏ a, ∏ k, f (w.occurrence a k).1 := by
  let e : (Σ a, Fin (π a)) ≃ Fin j :=
    (Equiv.sigmaCongrRight fun a ↦ (w.occurrence a).toEquiv).trans (Equiv.sigmaFiberEquiv w.1)
  exact (e.prod_comp f).symm.trans (Fintype.prod_sigma (fun i ↦ f (e i)))

/-- The product of position-dependent local table entries after sorting assignments by label. -/
theorem contraction_prod_blocks [Fintype A] [CommMonoid R]
    (w : WordsOfContent (Fin j) A π) {S : A → Type*}
    (entry : (a : A) → Fin j → S a → R) (v : (i : Fin j) → S (w.1 i)) :
    ∏ i, entry (w.1 i) i (v i) =
      ∏ a, ∏ k, entry a (w.occurrence a k).1 (w.assignmentEquiv S v a k) := by
  rw [prod_occurrences w]
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro k _
  rw [assignmentEquiv_apply]
  generalize w.occurrence a k = p
  rcases p with ⟨i, rfl⟩
  rfl

/-- Regroup the fixed-profile contraction into a sum over words and one common ordered
block-assignment space. Local entries may depend on the word and the original position. -/
theorem contraction_sum_blocks [Fintype A] [CommSemiring R]
    (π : A → ℕ) (j : ℕ) {S : A → Type*} [∀ a, Fintype (S a)]
    (entry : WordsOfContent (Fin j) A π → (a : A) → Fin j → S a → R) :
    (∑ v : (Σ w : WordsOfContent (Fin j) A π, (i : Fin j) → S (w.1 i)),
      ∏ i, entry v.1 (v.1.1 i) i (v.2 i)) =
      ∑ w : WordsOfContent (Fin j) A π, ∑ v : ((a : A) → Fin (π a) → S a),
        ∏ a, ∏ k, entry w a (w.occurrence a k).1 (v a k) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  apply Fintype.sum_equiv (w.assignmentEquiv S)
  exact contraction_prod_blocks w (entry w)

end WordsOfContent

end SpectralBooks
end LinearAlgebra
end OAI
