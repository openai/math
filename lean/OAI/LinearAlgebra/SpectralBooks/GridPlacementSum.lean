import OAI.LinearAlgebra.SpectralBooks.GridPlacement
import OAI.LinearAlgebra.SpectralBooks.BookCubePrices
import OAI.LinearAlgebra.SpectralBooks.TriangleWidth

/-! # The three original diagonal prices of a family of grid labels -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
open MeasureTheory

section

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The sum `a + b + c` on a binary diagonal, computed by the flat law in the original cube. -/
def sumPlacedDiagonal (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty) : ℝ :=
  meanWidth (S.image (gridPlacement none)) (hS.image _) +
    meanWidth (S.image (gridPlacement (some false))) (hS.image _) +
    meanWidth (S.image (gridPlacement (some true))) (hS.image _)

theorem sumPlacedDiagonal_pair (x y : DoubledGridSite ι n) :
    sumPlacedDiagonal {x,y} (Finset.insert_nonempty ..) = sumPlacedWires x y := by
  simp only [sumPlacedDiagonal, Finset.image_insert, Finset.image_singleton, meanWidth_pair, sumPlacedWires]

/-- In positive dimension the original cube has strictly positive diagonal price,
as required in the doubling theorem. Its corners include two distinct endpoints. -/
theorem innerCubeWidth_pos [Nonempty ι] : 0 < innerCubeWidth ι := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ (-1 : ℝ))
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))
  have hne : a ≠ b := by
    intro he
    have h := congrArg (fun x : EuclideanSpace ℝ ι ↦ x (Classical.arbitrary ι)) he
    norm_num [a, b] at h
  have hsub : ({a,b} : Finset _) ⊆ coordinateCubeCorners ι 1 := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨mem_coordinateCubeCorners_iff.mpr (fun _ ↦ Or.inl rfl),
      Finset.singleton_subset_iff.mpr (mem_coordinateCubeCorners_iff.mpr (fun _ ↦ Or.inr rfl))⟩
  have hmono : meanWidth {a,b} (Finset.insert_nonempty ..) ≤ innerCubeWidth ι := by
    unfold meanWidth innerCubeWidth
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply integral_mono (integrable_support _ _) (integrable_support _ _)
    intro u
    exact Finset.sup'_le _ _ (fun _ hx ↦ Finset.le_sup' _ (hsub hx))
  exact (dist_pos.mpr hne).trans_le ((meanWidth_pair a b) ▸ hmono)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
