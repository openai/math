import OAI.LinearAlgebra.SpectralBooks.Increment

/-!
# Conditioning a finite family of tips on a spine

These are the finite, deterministic inequalities used before taking
expectations in the proof of Theorem `thm:student`. Tips may coincide with each other or
with points of the spine.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {α ι : Type*} [DecidableEq α] {δ : Finset α → ℝ}

/-- The price of adding all the tips to the spine is bounded by the
sum of their individual increments at the spine. -/
theorem conditioning_union_image_le_of_nonempty
    (hmono : ∀ ⦃S T : Finset α⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.image_insert, Finset.union_insert, Finset.sum_insert hi]
    by_cases hx : tip i ∈ B ∪ s.image tip
    · rw [Finset.insert_eq_of_mem hx]
      have hinc : δ B ≤ δ (insert (tip i) B) := hmono hB (Finset.subset_insert _ _)
      linarith
    · have hinc := intersectingSubmodular_iff_diminishingIncrements.mp hsub
          (I := B) (A := B ∪ s.image tip) hB Finset.subset_union_left hx
      linarith

/-- Conditioning with monotonicity on all finite sets. -/
theorem conditioning_union_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  conditioning_union_image_le_of_nonempty (fun _ _ _ h => hmono h) hsub hB s tip

/-- The conditioning bound for the tips alone, including repeated tips. -/
theorem conditioning_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  (hmono Finset.subset_union_right).trans (conditioning_union_image_le hmono hsub hB s tip)

end SpectralBooks
end LinearAlgebra
end OAI
