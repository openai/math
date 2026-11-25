import OAI.LinearAlgebra.SpectralBooks.Book.BookNormal
import OAI.LinearAlgebra.SpectralBooks.SpineBall
import OAI.LinearAlgebra.SpectralBooks.SpineGaussian
import OAI.LinearAlgebra.SpectralBooks.Width
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Finite spine and page widths

The restriction of a Gaussian direction to the spine is its first coordinate.
A tip at height `a` contributes `a * z` to the maximum defining the support,
where `z` is the independent normal coordinate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support of points embedded horizontally in the Euclidean page. -/
theorem support_spine_base {B : Finset E} (h0 : 0 ∈ B) (u : Book.Lift E) :
    support (B.image Book.horizontal) (Finset.Nonempty.image ⟨0, h0⟩ _) u =
      spineSupport B u.ofLp.1 := by
  simp only [support, Finset.sup'_image, spineSupport, Finset.insert_eq_of_mem h0,
    Function.comp_apply, Book.horizontal, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    inner_zero_right, add_zero]
  congr 1
  funext x
  simp [Book.horizontal]

/-- The support after adjoining a page-normal tip to the finite spine. -/
theorem support_spine_tip {B : Finset E} (h0 : 0 ∈ B) (a : ℝ) (u : Book.Lift E) :
    support (insert (WithLp.toLp 2 (0, a)) (B.image Book.horizontal)) (Finset.insert_nonempty _ _) u =
      max (spineSupport B u.ofLp.1) (a * u.ofLp.2) := by
  calc
    _ = max ⟪u, WithLp.toLp 2 (0, a)⟫
        (support (B.image Book.horizontal) (Finset.Nonempty.image ⟨0, h0⟩ _) u) :=
      Finset.sup'_insert (Finset.Nonempty.image ⟨0, h0⟩ Book.horizontal) _
    _ = _ := by rw [support_spine_base h0, max_comm]; simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem meanWidth_page_integral
    (S : Finset (Book.Lift E)) (hS : S.Nonempty) :
    meanWidth S hS = Real.sqrt (2 * Real.pi) *
      ∫ w : E × ℝ, support S hS (WithLp.toLp 2 w) ∂spineGaussian E := by
  unfold meanWidth
  rw [← stdGaussian_prod_gaussianReal_map E]
  exact congrArg _ (integral_map_equiv (MeasurableEquiv.toLp 2 (E × ℝ)) (support S hS))


/-- Gaussian mean width of the finite spine alone, in the page coordinates. -/
theorem meanWidth_spine_base {B : Finset E} (h0 : 0 ∈ B) :
    meanWidth (B.image Book.horizontal) (Finset.Nonempty.image ⟨0, h0⟩ _) =
      Real.sqrt (2 * Real.pi) * ∫ w : E × ℝ, spineSupport B w.1 ∂spineGaussian E := by
  rw [meanWidth_page_integral]
  simp only [support_spine_base h0]

/-- Gaussian mean width of the finite spine together with the tip of height `a`. -/
theorem meanWidth_spine_tip {B : Finset E} (h0 : 0 ∈ B) (a : ℝ) :
    meanWidth (insert (WithLp.toLp 2 (0, a)) (B.image Book.horizontal)) (Finset.insert_nonempty _ _) =
      Real.sqrt (2 * Real.pi) * ∫ w : E × ℝ, max (spineSupport B w.1) (a * w.2)
        ∂spineGaussian E := by
  rw [meanWidth_page_integral]
  simp only [support_spine_tip h0]

/-- The spine-ball bound assuming the finite diagonal law on each of the individual pages. -/
theorem diagonal_le_spineBall_of_meanWidth {X ι : Type*} [DecidableEq X] [Fintype ι]
    (δ : Finset X → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    (spine : E → X) (tip : ι → X) (a : ι → ℝ)
    (hbase : ∀ (B : Finset E) (h0 : 0 ∈ B), (∀ x ∈ B, ‖x‖ ≤ 1) →
      δ (B.image spine) = meanWidth (B.image Book.horizontal) (Finset.Nonempty.image ⟨0, h0⟩ _))
    (hpage : ∀ (i : ι) (B : Finset E), 0 ∈ B → (∀ x ∈ B, ‖x‖ ≤ 1) →
      δ (insert (tip i) (B.image spine)) =
        meanWidth (insert (WithLp.toLp 2 (0, a i)) (B.image Book.horizontal))
          (Finset.insert_nonempty _ _)) :
    δ (Finset.univ.image tip) ≤ Real.sqrt (2 * Real.pi) * spineBallExpectation E a :=
  diagonal_le_spineBall δ hmono hsub spine tip a
    (fun B h0 hB => (hbase B h0 hB).trans (meanWidth_spine_base h0))
    (fun i B h0 hB => (hpage i B h0 hB).trans (meanWidth_spine_tip h0 (a i)))

end SpectralBooks
end LinearAlgebra
end OAI
