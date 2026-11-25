import OAI.LinearAlgebra.SpectralBooks.Dual
import OAI.LinearAlgebra.SpectralBooks.Midpoint
import OAI.LinearAlgebra.SpectralBooks.Norm
import OAI.LinearAlgebra.SpectralBooks.NormPatch
import OAI.LinearAlgebra.SpectralBooks.SectorRays
import OAI.LinearAlgebra.SpectralBooks.Shorten

/-! # From shifted crossing costs to spectral curvature

The shifted crossing bounds imply rigidity of the norm on every finite-dimensional
spectral normed patch. Applying rigidity to tangent sectors gives CAT(0) for
a geodesic spectral space satisfying Busemann comparison together with its blow-ups.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction

/-- The two crossed placements force the norm to come from a real inner product. -/
theorem ShiftedCrossingCost.innerProductSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (cost : ShiftedCrossingCost E) :
    Nonempty (InnerProductSpace ℝ E) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    refine ⟨InnerProductSpace.ofNorm ℝ (fun a b ↦ ?_)⟩
    simp [Subsingleton.elim a 0, Subsingleton.elim b 0]
  | inr h =>
    apply innerProductSpace_of_dualBallParallelogramLe
    exact fun t u ht hu ↦ dualBall_crossingBound_of_smooth t u
      (fun _ _ _ _ hx hy hf hg ↦ cost.smooth_dual hx hy hf hg ht hu)

/-- A common start in Busemann's four-endpoint estimate gives radial contraction. -/
theorem SectorBusemann.radial {X : Type*} [MetricSpace X]
    (hB : SectorBusemann X) : RadialBusemann X := by
  intro o x y a b ha hb t ht
  have hf {p : X} {r : ℝ → X} (hr : IsSegment r o p) : SectorFraction o p (r t) t := by
    refine ⟨hr.dist_from_source ht, ?_⟩
    have hh := hr.2.2 t ht 1 (by norm_num)
    simpa [hr.2.1, abs_of_nonpos (sub_nonpos.mpr ht.2)] using hh
  simpa using hB o x o y (a t) (b t) t ht (hf ha) (hf hb)

variable {K X : Type*} [Field K] [MetricSpace X]

/-- A positively scaled realization of each finite configuration suffices for
norm rigidity in a spectral space, given the two-cut asymptotic price comparison. -/
theorem SpectralPlacementPrices.normRigidity_of_shiftedCost
    (P : SpectralPlacementPrices K X)
    (hc : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      SpectralPlacementPrices K E → ShiftedCrossingCost E) : ScaledSectorNormRigidity X := by
  intro E _ _ _ h
  obtain ⟨Q⟩ := spectralPrices_of_finite_scaled_models h P
  exact (hc E Q).innerProductSpace

/-- Whole-segment comparison follows from the crossed-wire cost test in each normed
space and Busemann convexity both in the space and in its infinitesimal rescalings. -/
theorem SpectralPlacementPrices.catZero_of_shiftedCost (P : SpectralPlacementPrices K X)
    (g : IsGeodesic X) (hB : SectorBusemann X)
    (hB' : ∀ o : X, SectorBusemann (CurvatureBlowup.Space o))
    (hc : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      SpectralPlacementPrices K E → ShiftedCrossingCost E) : CATZero X := by
  apply catZero_of_quadratic_blowups g hB.radial
  intro o
  apply quadraticRaySectors_of_normRigidity (CurvatureBlowup.isGeodesic g o) (hB' o)
  intro E _ _ _ hE
  let Q := Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos o P
  obtain ⟨R⟩ := hE.spectralPrices Q
  exact (hc E R).innerProductSpace

end SpectralBooks
end LinearAlgebra
end OAI
