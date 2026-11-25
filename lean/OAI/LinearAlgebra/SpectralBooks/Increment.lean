import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Intersecting submodularity of diagonal prices

The proof of Lemma `lem:submod` in the manuscript uses two integer weight
specializations to obtain a one-site inequality. We verify the weights on
their specified supports and the telescoping argument for finite sets.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset

section Increments

variable {α : Type*} [DecidableEq α] (δ : Finset α → ℝ)

/-- The one-site inequality (equation `eq:width-increment`). -/
def DiminishingIncrements : Prop :=
  ∀ ⦃I A : Finset α⦄ ⦃z : α⦄, I.Nonempty → I ⊆ A → z ∉ A →
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I

/-- The price inequality for finite sets with nonempty intersection. -/
def IntersectingSubmodular : Prop :=
  ∀ ⦃A B : Finset α⦄, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B

variable {δ}

/-- Adjoin a finite family of new sites successively to both sets. -/
theorem diminishingIncrements_union (h : DiminishingIncrements δ)
    {I A : Finset α} (hne : I.Nonempty) (hIA : I ⊆ A)
    (S : Finset α) (hdis : Disjoint S A) :
    δ (A ∪ S) - δ A ≤ δ (I ∪ S) - δ I := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    obtain ⟨hzA, hSA⟩ := Finset.disjoint_insert_left.mp hdis
    have step := h (I := I ∪ S) (A := A ∪ S) (z := z) (hne.mono (Finset.subset_union_left (s₂ := S)))
      (Finset.union_subset_union hIA (Finset.Subset.refl S))
      (by simpa only [Finset.mem_union, not_or] using And.intro hzA hz)
    rw [Finset.union_insert, Finset.union_insert]
    linarith [ih hSA]

/-- Intersecting submodularity is equivalent to the one-site increment inequality. -/
theorem intersectingSubmodular_iff_diminishingIncrements :
    IntersectingSubmodular δ ↔ DiminishingIncrements δ := by
  constructor
  · intro h I A z hI hIA hz
    have hinter : A ∩ insert z I = I := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    have hunion : A ∪ insert z I = insert z A := by
      rw [Finset.union_insert, Finset.union_eq_left.mpr hIA]
    have h' := h (A := A) (B := insert z I) (by simpa only [hinter] using hI)
    rw [hinter, hunion] at h'
    linarith
  · intro h A B hAB
    have h' := diminishingIncrements_union h hAB Finset.inter_subset_left
      (B \ A) Finset.sdiff_disjoint
    have heq : (A ∩ B) ∪ (B \ A) = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      grind
    rw [heq, Finset.union_sdiff_self_eq_union] at h'
    linarith

end Increments

section IntegerWeights

variable {ι : Type*} [Fintype ι]

/-- On the support selected by coefficient extraction, the first local
weights sum to `(g - h)²`. Here `ι` indexes the sites other than site 1. -/
theorem firstWeight_eq_sq (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = (g - h) ^ 2 := by
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hs]
  ring

/-- The first specialization retains precisely `g = h`. -/
theorem firstWeight_eq_zero_iff (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = 0 ↔ g = h := by
  rw [firstWeight_eq_sq g h v₁ v hs]
  simp [sub_eq_zero]

/-- On the remaining support, the second local weights also sum to a
sum of squares in the integers. -/
theorem secondWeight_eq_sum_sq (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = ∑ j, (v j - v₁) ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_right_comm (2 : ℤ) _ v₁]
  rw [← Finset.mul_sum, hs]
  simp
  ring

/-- The second specialization retains precisely the common choices of all labels. -/
theorem secondWeight_eq_zero_iff (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = 0 ↔ ∀ j, v j = v₁ := by
  rw [secondWeight_eq_sum_sq v₁ v hs, Finset.sum_sq_eq_zero_iff]
  simp [sub_eq_zero]

end IntegerWeights

end SpectralBooks
end LinearAlgebra
end OAI
