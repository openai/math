import OAI.LinearAlgebra.SpectralBooks.Increment

/-!
# Independence across the two doubled cubes

This is the finite-set argument in equation `eq:book-independence`. A
diagonal price is defined on nonempty finite sets. The overlap of the
two pages contains the corners of the common inner cube.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {α : Type*} [DecidableEq α] {δ : Finset α → ℝ}

/-- For a monotone price, intersecting submodularity gives diminishing
returns for adjoining any finite set, including sets that meet the base. -/
theorem intersectingSubmodular_union_increment (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    {I A : Finset α} (hne : I.Nonempty) (hIA : I ⊆ A) (S : Finset α) :
    δ (A ∪ S) - δ A ≤ δ (I ∪ S) - δ I := by
  have hI : I ⊆ A ∩ (I ∪ S) := Finset.subset_inter hIA Finset.subset_union_left
  have hh := hs (hne.mono hI)
  rw [← Finset.union_assoc, Finset.union_eq_left.mpr hIA] at hh
  linarith [hm hne hI]

/-- In both larger cubes, adjoining the inner corners and finitely many points
of the cube to its outer corners has price at most `2D`. The inner corners have price
`D`, and all corners together have price at least `3D`. These corner prices imply the
book independence equation for the finite sets `L` and `N`. -/
theorem book_independence_of_corner_bounds (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (K B C L N : Finset α) (hK : K.Nonempty) (D : ℝ)
    (hinner : δ K = D) (hleft : δ (K ∪ L ∪ B) ≤ 2 * D)
    (hright : δ (K ∪ N ∪ C) ≤ 2 * D) (hboth : 3 * D ≤ δ (K ∪ B ∪ C)) :
    δ (K ∪ L ∪ N) = δ (K ∪ L) + δ (K ∪ N) - δ K := by
  have hL := intersectingSubmodular_union_increment hs hm hK
    (Finset.subset_union_left (s₁ := K) (s₂ := L)) N
  have hB := intersectingSubmodular_union_increment hs hm
    (hK.mono (Finset.subset_union_left (s₂ := L)))
    (Finset.subset_union_left (s₁ := K ∪ L) (s₂ := N)) B
  have hNC : K ∪ N ⊆ K ∪ L ∪ N ∪ B := by
    apply Finset.union_subset
    · exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · exact Finset.subset_union_right.trans Finset.subset_union_left
  have hC := intersectingSubmodular_union_increment hs hm
    (hK.mono (Finset.subset_union_left (s₂ := N))) hNC C
  have hcover : K ∪ B ∪ C ⊆ K ∪ L ∪ N ∪ B ∪ C := by
    exact Finset.union_subset_union_left
      (Finset.union_subset_union_left
        (Finset.subset_union_left.trans Finset.subset_union_left))
  have lower := hm (hK.mono (Finset.subset_union_left.trans Finset.subset_union_left)) hcover
  linarith

/-- In both larger cubes, adjoining the inner corners and finitely many points
of the cube to its outer corners has price `2D`. The inner corners have price
`D`, and all corners together have price `3D`. These corner prices imply the
book independence equation for the finite sets `L` and `N`. -/
theorem book_independence (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (K B C L N : Finset α) (hK : K.Nonempty) (D : ℝ)
    (hinner : δ K = D) (hleft : δ (K ∪ L ∪ B) = 2 * D)
    (hright : δ (K ∪ N ∪ C) = 2 * D) (hboth : δ (K ∪ B ∪ C) = 3 * D) :
    δ (K ∪ L ∪ N) = δ (K ∪ L) + δ (K ∪ N) - δ K :=
  book_independence_of_corner_bounds hs hm K B C L N hK D hinner hleft.le hright.le hboth.ge

end SpectralBooks
end LinearAlgebra
end OAI
