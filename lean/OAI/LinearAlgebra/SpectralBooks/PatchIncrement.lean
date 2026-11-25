import OAI.LinearAlgebra.SpectralBooks.Increment
import Mathlib.Analysis.Convex.Hull

/-! # Bounding the price of an insertion by its price on an inner patch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

/-- Monotonicity extends the one-site inequality to insertions already present in the
larger configuration. -/
theorem price_increment_le_of_subset {α : Type*} (δ : Finset α → ℝ)
    (hmono : ∀ ⦃S T : Finset α⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ) {I A : Finset α}
    (hI : I.Nonempty) (hIA : I ⊆ A) (z : α) :
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I := by
  by_cases hz : z ∈ A
  · rw [Finset.insert_eq_of_mem hz, sub_self, sub_nonneg]
    exact hmono hI (Finset.subset_insert z I)
  · exact intersectingSubmodular_iff_diminishingIncrements.mp hsub hI hIA hz

/-- If every point of the patch lies in the convex hull of the configuration,
its insertion cost bounds the insertion cost for the whole configuration. -/
theorem price_increment_le_of_hull_patch {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    {S P : Finset E}
    (hhull : ∀ T : Finset E, (T : Set E) ⊆ convexHull ℝ (S : Set E) → δ (S ∪ T) = δ S)
    (hP : P.Nonempty)
    (hPS : (P : Set E) ⊆ convexHull ℝ (S : Set E)) (z : E) :
    δ (insert z S) - δ S ≤ δ (insert z P) - δ P := by
  have h := price_increment_le_of_subset δ hmono hsub hP (Finset.subset_union_right (s₁ := S)) z
  rw [hhull P hPS] at h
  exact (sub_le_sub_right (hmono (Finset.insert_nonempty z S)
    (Finset.insert_subset_insert z Finset.subset_union_left)) _).trans h

end SpectralBooks
end LinearAlgebra
end OAI
