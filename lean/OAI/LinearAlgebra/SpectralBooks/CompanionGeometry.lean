import OAI.LinearAlgebra.SpectralBooks.BorderStretchConsequences
import OAI.LinearAlgebra.SpectralBooks.StudentTestFromFlat

/-! # Geometric alternatives at the graph interface of the companion stretch theorem -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter HyperbolicObstruction

/-- A two-dimensional profile shortening forces a hard subcubic grid in the tree case.
Tree compression then supplies a non-tree spectral metric. -/
theorem hasNonTreeWireMetric_of_profile_grid_stretch (K : Type) [Field K] [Infinite K]
    (stretch : Crossing.HasProfileShortening K 2 → ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids K δ) :
    HasNonTreeWireMetric K := by
  by_contra tree
  obtain ⟨δ, pos, hard⟩ := stretch (hasProfileShortening_of_tree tree)
  exact tree (hasNonTreeWireMetric_of_hardSubcubicGrids pos hard)

/-- The unbounded-dimensional flat case supplies the finite Gaussian tests. A missing
flat supplies the positive-width paid crossing of the companion manuscript. -/
theorem gaussianMatrixTest_or_profile_shortening (K : Type) [Field K] :
    GaussianMatrixTest K ∨ ∃ D : ℕ, 2 ≤ D ∧ Crossing.HasProfileShortening K D := by
  classical
  have curvature : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices K X →
      IsGeodesic X → CATZero X := fun _ _ _ Q hg => Q.catZero hg
  by_cases flat : ∀ D : ℕ, 2 ≤ D → Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D)))
  · left
    apply gaussianMatrixTest_of_unbounded_student
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop 2] with D hD
    exact studentMatrixTest_of_spectral_flat K curvature hD (flat D hD)
  · right
    obtain ⟨D, failed⟩ := not_forall.mp flat
    have hD : 2 ≤ D := Classical.byContradiction fun small => failed fun good => (small good).elim
    have missing : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D))) :=
      fun present => failed fun _ => present
    obtain ⟨m, hm, shortening⟩ := shortenedCrossing_of_no_flat K hD
      (hasSpectralAxisExtensions_of_curvature K curvature D) missing
    exact ⟨D, hD, shortening.hasProfileShortening hD hm⟩

end SpectralBooks
end LinearAlgebra
end OAI
