import OAI.LinearAlgebra.SpectralBooks.DoubledGridPrices

/-! # Diagonal price on an arbitrary subset of one private grid -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical

section

variable {ι : Type*} [Fintype ι]

/-- In a single page the private sites are either at half scale or at zero. -/
private theorem meanWidth_private_placement (n : ℕ) (page : Option Bool) (k : Bool)
    (T : Finset (cubeGrid ι n)) (hT : T.Nonempty) :
    meanWidth ((T.image (gridLabel k)).image (gridPlacement page)) ((hT.image _).image _) =
      (if page = none ∨ page = some k then (1 / 2 : ℝ) else 0) *
        meanWidth (T.image Subtype.val) (hT.image _) := by
  let r : ℝ := if page = none ∨ page = some k then 1 / 2 else 0
  have hr : 0 ≤ r := by dsimp [r]; split <;> norm_num
  have he : (T.image (gridLabel k)).image (gridPlacement page) =
      (T.image Subtype.val).image (fun x : EuclideanSpace ℝ ι ↦ r • x) := by
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x _
    by_cases h : page = none ∨ page = some k <;> simp [r, h]
  simp only [he]
  convert! meanWidth_smul (T.image Subtype.val) (hT.image _) hr using 2
  ext x
  simp only [Finset.mem_image]

/-- Two active half-scale placements and one zero placement sum to the
Euclidean width of any nonempty subset of one private grid. -/
theorem sumPlacedDiagonal_gridLabel_image (n : ℕ) (k : Bool) (T : Finset (cubeGrid ι n))
    (hT : T.Nonempty) :
    sumPlacedDiagonal (T.image (gridLabel k)) (hT.image _) =
      meanWidth (T.image Subtype.val) (hT.image _) := by
  cases k <;> simp [sumPlacedDiagonal, meanWidth_private_placement n _ _ T hT] <;> ring

namespace DoubledGridPrices

variable {X : ℕ → Type*} [∀ n, MetricSpace (X n)] (P : DoubledGridPrices ι X)

/-- The selected price restricted to one private grid agrees with Gaussian
mean width on every nonempty subset of its Euclidean coordinates. -/
theorem private_grid_price (n : ℕ) (k : Bool) (T : Finset (cubeGrid ι n)) (hT : T.Nonempty) :
    P.diagonal n (T.image (P.family.site n k)) = meanWidth (T.image Subtype.val) (hT.image _) := by
  have h := P.private_eq n k (T.image (gridLabel k)) (hT.image _)
    (Finset.image_mono _ (Finset.subset_univ T))
  rw [sumPlacedDiagonal_gridLabel_image n k T hT, Finset.image_image] at h
  exact h

end DoubledGridPrices
end

end SpectralBooks
end LinearAlgebra
end OAI
