import OAI.LinearAlgebra.SpectralBooks.BookSlabs
import OAI.LinearAlgebra.SpectralBooks.CrossDistance

/-!
# A three-page Euclidean book from doubled cubes

The normal-cone integral comparison gives the reflected distance between the
outward slabs. Together with the common inward slab this realizes a bounded
book. Magnifying about its spine gives an entire Euclidean book in a pointed
ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Book Filter MeasureTheory Set

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MetricSpace X]

variable [MeasurableSpace (LiftSphere (EuclideanSpace ℝ (Option ι)))]
    [BorelSpace (LiftSphere (EuclideanSpace ℝ (Option ι)))]
    (σ : Measure (LiftSphere (EuclideanSpace ℝ (Option ι)))) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (hX : SharpIntegralFillings.IsCAT0 X) {b c : EuclideanSpace ℝ (Option ι) → X}
    (hb : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube _ 1).EqOn b c)
    (hcmp : ∀ p ∈ upperUnitCubeFacet (none : Option ι),
      (∀ j, j ≠ none → p j ∈ Ioo (-1 : ℝ) 1) → ∀ r ∈ Ioc (0 : ℝ) 1,
        FacetOutwardComparison σ none (fun w ↦ dist (c w) (b (p + r • EuclideanSpace.single none 1))))

include σ hX hb hc hbc hcmp

/-- Two doubled cube charts in a CAT(0) space with the manuscript's
normal-cone comparison contain the bounded three-page book over the unit
spine ball. -/
theorem exists_boundedBook_of_outward_comparison :
    ∃ f : boundedBook (EuclideanSpace ℝ ι) → X, Isometry f := by
  apply exists_isometry_boundedBook_of_cross_distances hb hc hbc
  intro p q hp hq r s hr hs
  exact doubled_cube_cross_distance σ hX hb hc hbc hcmp hp hq hr hs

/-- Along every ultrafilter tending to infinity, magnifications of the doubled
charts about the common spine center contain an isometric copy of the entire
three-page book. -/
theorem exists_book_blowup_of_outward_comparison (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ f : boundedBook (EuclideanSpace ℝ ι) → X, Isometry f ∧
      ∃ g : Book (EuclideanSpace ℝ ι) → IntegerBlowup U (f boundedBookOrigin), Isometry g := by
  obtain ⟨f, hf⟩ := exists_boundedBook_of_outward_comparison σ hX hb hc hbc hcmp
  exact ⟨f, hf, isometry_integerBlowup_of_boundedBook f hf U hU⟩

end SpectralBooks
end LinearAlgebra
end OAI
