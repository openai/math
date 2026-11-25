import OAI.LinearAlgebra.SpectralBooks.Book
import OAI.LinearAlgebra.SpectralBooks.SpinePageWidth

/-!
# The spine-ball inequality for the three-page book

The union of a page and a second page is a full Euclidean flat. Applying
the finite flat diagonal law on each such flat supplies the two support
integrals used in the bound for the tips.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Equation `eq:spine-ball` for actual book points, under the flat
diagonal law and the monotone, intersecting-submodular diagonal price. -/
theorem book_tips_le_spineBall (δ : Finset (Book E) → ℝ) (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ)
    (hflat : ∀ (e : Book.Lift E → Book E), Isometry e →
      ∀ (S : Finset (Book.Lift E)) (hS : S.Nonempty), δ (S.image e) = meanWidth S hS)
    (a : Fin 3 → ℝ≥0) :
    δ (Finset.univ.image (fun i ↦ bookPoint i (a i) (0 : E))) ≤
      Real.sqrt (2 * Real.pi) * spineBallExpectation E (fun i ↦ (a i : ℝ)) := by
  let spine (x : E) := bookPoint 0 0 x
  have hbaseImage (i j : Fin 3) (B : Finset E) :
      (B.image Book.horizontal).image (bookPlane i j) = B.image spine := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p _
    exact (bookPlane_nonneg i j p 0).trans (bookPoint_zero i 0 p)
  apply diagonal_le_spineBall_of_meanWidth δ hmono hsub spine
  · intro B h0 _
    rw [← hbaseImage 0 1]
    exact hflat _ (bookPlane_isometry (by decide : (0 : Fin 3) ≠ 1)) _ _
  · intro i B h0 _
    obtain ⟨j, hji⟩ := exists_ne i
    have hp := hflat _ (bookPlane_isometry hji.symm)
      (insert (WithLp.toLp 2 (0, (a i : ℝ))) (B.image Book.horizontal)) (Finset.insert_nonempty _ _)
    simpa only [Finset.image_insert, bookPlane_nonneg, hbaseImage] using hp

end

end

end SpectralBooks
end LinearAlgebra
end OAI
