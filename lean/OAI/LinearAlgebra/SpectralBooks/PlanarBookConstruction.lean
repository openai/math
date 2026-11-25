import OAI.LinearAlgebra.SpectralBooks.BookConstruction
import OAI.LinearAlgebra.SpectralBooks.BookDilationPrices

/-! # Spectral placement prices on the planar book

In the square case the tangent coordinate of the common facet is scalar.
The singleton orthonormal basis identifies it with the real line, preserving
the unit spine ball. The bounded book inside the two squares therefore
induces placement prices for every finite tensor on the full planar book.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Book MeasureTheory Set

/-- Scalar coordinates on a Euclidean space with one axis. -/
private def singletonSpineEquiv (ι : Type*) [Unique ι] [Fintype ι] [DecidableEq ι] :
    ℝ ≃ᵢ EuclideanSpace ℝ ι where
  toFun := EuclideanSpace.single default
  invFun := (· default)
  left_inv x := by simp
  right_inv x := by
    apply PiLp.ext
    intro i
    rw [Unique.eq_default i]
    simp
  isometry_toFun := Isometry.of_dist_eq (PiLp.dist_single_same 2 (fun _ : ι ↦ ℝ) default)

/-- Identifying the singleton Euclidean spine with the real line leaves all
three rays and their heights fixed. -/
def planarBookEquiv (ι : Type*) [Unique ι] [Fintype ι] [DecidableEq ι] :
    Book ℝ ≃ᵢ Book (EuclideanSpace ℝ ι) :=
  IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Tripod)
    (singletonSpineEquiv ι)

/-- The singleton-coordinate identification carries the bounded planar book
onto the bounded Euclidean-coordinate book. -/
def boundedPlanarBookEquiv (ι : Type*) [Unique ι] [Fintype ι] [DecidableEq ι] :
    boundedBook ℝ ≃ᵢ boundedBook (EuclideanSpace ℝ ι) where
  toEquiv := (planarBookEquiv ι).toEquiv.subtypeEquiv (fun x ↦ by
    change (‖x.fst.val‖ ≤ 1 ∧ ‖x.snd‖ ≤ 1) ↔
      (‖x.fst.val‖ ≤ 1 ∧ ‖EuclideanSpace.single (ι := ι) default x.snd‖ ≤ 1)
    rw [PiLp.norm_single])
  isometry_toFun := fun x y ↦ (planarBookEquiv ι).isometry x.val y.val

/-- Spectral placement prices over the original field on the planar book,
obtained from two doubled squares obeying the normal-cone comparison. -/
theorem exists_planarBook_prices_of_outward_comparison {K ι X : Type*}
    [Field K] [Unique ι] [Fintype ι] [DecidableEq ι] [MetricSpace X]
    [MeasurableSpace (LiftSphere (EuclideanSpace ℝ (Option ι)))]
    [BorelSpace (LiftSphere (EuclideanSpace ℝ (Option ι)))]
    (σ : Measure (LiftSphere (EuclideanSpace ℝ (Option ι)))) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (P : SpectralPlacementPrices K X) (hX : SharpIntegralFillings.IsCAT0 X)
    {b c : EuclideanSpace ℝ (Option ι) → X}
    (hb : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (b u) (b v) = dist u v)
    (hc : ∀ u ∈ coordinateCube _ 2, ∀ v ∈ coordinateCube _ 2, dist (c u) (c v) = dist u v)
    (hbc : (coordinateCube _ 1).EqOn b c)
    (hcmp : ∀ p ∈ upperUnitCubeFacet (none : Option ι),
      (∀ j, j ≠ none → p j ∈ Ioo (-1 : ℝ) 1) → ∀ r ∈ Ioc (0 : ℝ) 1,
        FacetOutwardComparison σ none (fun w ↦ dist (c w) (b (p + r • EuclideanSpace.single none 1)))) :
    Nonempty (SpectralPlacementPrices K (Book ℝ)) := by
  obtain ⟨f, hf⟩ := exists_boundedBook_of_outward_comparison σ hX hb hc hbc hcmp
  exact ⟨P.bookOfIsometry (f ∘ boundedPlanarBookEquiv ι) (hf.comp (boundedPlanarBookEquiv ι).isometry)⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
