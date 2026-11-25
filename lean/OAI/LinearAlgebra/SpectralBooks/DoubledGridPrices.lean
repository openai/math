import OAI.LinearAlgebra.SpectralBooks.GridPlacementSum
import OAI.LinearAlgebra.SpectralBooks.GridPlacementWidth
import OAI.LinearAlgebra.SpectralBooks.GridCornerPrice

/-! # The diagonal prices in the finite doubled-grid construction

The inputs are the diagonal evaluations of the price selected by the doubling
theorem, after placement in a metric space preserving its wire distances. The
three old prices are written as the widths of their Euclidean placements. From
the private and joint equalities we compute the price of the fixed number of
corners and centers in every grid.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

section

/-- The diagonal consequences of doubling at `λ = 1`, for the three concrete
placements on the grids. Local distances are the binary wire prices. -/
structure DoubledGridPrices (ι : Type*) [Fintype ι] (X : ℕ → Type*) [∀ n, MetricSpace (X n)] where
  place : ∀ n, DoubledGridSite ι n → X n
  diagonal : ∀ n, Finset (X n) → ℝ
  wire : ∀ n x y, diagonal n {x, y} = dist x y
  mono : ∀ n ⦃S T⦄, S.Nonempty → S ⊆ T → diagonal n S ≤ diagonal n T
  submod : ∀ n, IntersectingSubmodular (diagonal n)
  upper : ∀ n (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty),
    diagonal n (S.image (place n)) ≤ sumPlacedDiagonal S hS
  private_eq : ∀ n k (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty), S ⊆ gridLabels ι n k →
    diagonal n (S.image (place n)) = sumPlacedDiagonal S hS
  joint_eq : ∀ n, let S := gridLabels ι n false ∪ gridLabels ι n true
    diagonal n (S.image (place n)) = sumPlacedDiagonal S ((gridLabels_nonempty ι n false).mono Finset.subset_union_left)

namespace DoubledGridPrices

variable {ι : Type*} [Fintype ι] {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    (P : DoubledGridPrices ι X)

/-- Realize the two finite, privately doubled grids and their auxiliary midpoints. -/
def family : DoubledGridFamily ι (fun n ↦ P.place n gridCenter) :=
  doubledGridFamilyOfWires P.place (by
    intro n s t
    have h := P.upper n {s,t} (Finset.insert_nonempty ..)
    simpa only [Finset.image_insert, Finset.image_singleton, P.wire, sumPlacedDiagonal_pair] using h)
    (by
      intro n k x y
      have hsub : {gridLabel k x, gridLabel k y} ⊆ gridLabels ι n k := by
        apply Finset.insert_subset_iff.mpr
        exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
          Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
      have h := P.private_eq n k _ (Finset.insert_nonempty ..) hsub
      simpa only [Finset.image_insert, Finset.image_singleton, P.wire, sumPlacedDiagonal_pair] using h)

theorem image_gridLabels (n : ℕ) (k : Bool) :
    (gridLabels ι n k).image (P.place n) = P.family.gridSites n k := by
  simp only [gridLabels, Finset.image_image, DoubledGridFamily.gridSites]
  rfl

theorem image_cornerLabels (n : ℕ) (k : Bool) :
    (cornerLabels ι n k).image (P.place n) = P.family.cornerSites n k := by
  simp only [cornerLabels, Finset.image_insert, Finset.image_image, DoubledGridFamily.cornerSites]
  rfl

/-- Each full private grid has twice the original cube price. -/
theorem grid_price (n : ℕ) (k : Bool) : P.diagonal n (P.family.gridSites n k) = 2 * innerCubeWidth ι := by
  rw [← P.image_gridLabels, P.private_eq n k _ (gridLabels_nonempty ι n k) Finset.Subset.rfl]
  cases k <;> simp [sumPlacedDiagonal, meanWidth_gridLabels] <;> ring

/-- The price of each private grid is attained on its center and corners. -/
theorem corner_price (n : ℕ) (k : Bool) : P.diagonal n (P.family.cornerSites n k) = 2 * innerCubeWidth ι := by
  rw [← P.image_cornerLabels, P.private_eq n k _ (cornerLabels_nonempty ι n k) (cornerLabels_subset_gridLabels ι n k)]
  cases k <;> simp [sumPlacedDiagonal, meanWidth_cornerLabels] <;> ring

/-- The doubled price of all grid indices is the sum of three full cube widths. -/
theorem grid_union_price (n : ℕ) :
    P.diagonal n (P.family.gridSites n false ∪ P.family.gridSites n true) = 3 * innerCubeWidth ι := by
  have h := P.joint_eq n
  simp only [Finset.image_union, P.image_gridLabels] at h
  rw [h, sumPlacedDiagonal, meanWidth_gridLabels_union, meanWidth_gridLabels_union, meanWidth_gridLabels_union]
  ring

/-- The mixed price is already attained by the two finite sets of corners and the shared center,
with the same number of labels for every mesh. -/
theorem corner_union_price (n : ℕ) :
    P.diagonal n (P.family.cornerSites n false ∪ P.family.cornerSites n true) = 3 * innerCubeWidth ι := by
  rw [← P.family.grid_union_price_eq_corner_union_price n (P.diagonal n) (P.submod n) (P.mono n)
    (fun k ↦ (P.corner_price n k).trans (P.grid_price n k).symm)]
  exact P.grid_union_price n

end DoubledGridPrices
end

end

end SpectralBooks
end LinearAlgebra
end OAI
