import OAI.LinearAlgebra.FiniteFourier.DirectionalPrice
import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Simultaneously homogeneous spectral prices on a Euclidean plane

All tensors, basis dimensions and site configurations use one blowup based
at the origin, with scale `1/(n+1)`. Convexity in the placements identifies
each of these ultralimits with an ordinary one-sided directional derivative.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Filter Set
open scoped Topology

noncomputable section

variable {K E : Type*} [Field K] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Distances are rescaled by `n+1` in the blowup at the origin. -/
def tangentPlaneScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tangentPlaneScale_pos (n : ℕ) : 0 < tangentPlaneScale n := by
  unfold tangentPlaneScale
  positivity

theorem tendsto_tangentPlaneScale : Tendsto tangentPlaneScale atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall tangentPlaneScale_pos⟩

private theorem rescaled_dist_tendsto (p q : E) :
    Tendsto (fun n : ℕ ↦ dist (tangentPlaneScale n • p) (tangentPlaneScale n • q) /
      tangentPlaneScale n) (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ) (𝓝 (dist p q)) := by
  apply tendsto_const_nhds.congr
  intro n
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (tangentPlaneScale_pos n)]
  field_simp [(tangentPlaneScale_pos n).ne']

/-- Spectral placement on the same normed space, obtained by blowing up the
original price assignment at the origin along a single ultrafilter. -/
def tangentPlane (P : SpectralPlacementPrices K E) : SpectralPlacementPrices K E :=
  P.blowup (Ultrafilter.of atTop) tangentPlaneScale tangentPlaneScale_pos
    (fun n p ↦ tangentPlaneScale n • p) 0 rescaled_dist_tendsto

/-- Every finite tensor and placement has the specified limit in the same
spectral assignment on the blown-up plane. -/
theorem tendsto_tangentPlane_price (P : SpectralPlacementPrices K E) {I : Type} [Fintype I]
    (T : Raw.{0} I K) (x : I → E) :
    Tendsto (fun n : ℕ ↦ P.price T (tangentPlaneScale n • x) / tangentPlaneScale n)
      (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ) (𝓝 ((tangentPlane P).price T x)) :=
  SpectralPlacementPrices.tendsto_blowupFamily_price (fun _ ↦ P) (Ultrafilter.of atTop)
    tangentPlaneScale tangentPlaneScale_pos (fun n p ↦ tangentPlaneScale n • p)
    0 rescaled_dist_tendsto T x

/-- When the original price is jointly convex, the price of an individual
placement in the new plane equals its actual directional derivative. -/
theorem tangentPlane_price_eq_directionalPrice (P : SpectralPlacementPrices K E)
    {I : Type} [Fintype I] (T : Raw.{0} I K) (hc : ConvexOn ℝ univ (P.price T)) (x : I → E) :
    (tangentPlane P).price T x = directionalPrice (P.price T) x := by
  apply tendsto_nhds_unique (tendsto_tangentPlane_price P T x)
  exact ((tendsto_directionalPrice hc (P.collapsed T 0) x).comp tendsto_tangentPlaneScale).mono_left
    (Ultrafilter.of_le _)

/-- The rescaled price converges along every positive scale tending to zero. -/
theorem tendsto_tangentPlane_price_of_convexOn (P : SpectralPlacementPrices K E)
    {I : Type} [Fintype I] (T : Raw.{0} I K) (hc : ConvexOn ℝ univ (P.price T)) (x : I → E) :
    Tendsto (fun t : ℝ ↦ P.price T (t • x) / t) (𝓝[>] 0) (𝓝 ((tangentPlane P).price T x)) := by
  rw [tangentPlane_price_eq_directionalPrice P T hc x]
  exact tendsto_directionalPrice hc (P.collapsed T 0) x

/-- The single new spectral placement has positively homogeneous, jointly
subadditive prices for every raw tensor whose original price is jointly convex. -/
theorem tangentPlane_sublinear (P : SpectralPlacementPrices K E) {I : Type} [Fintype I]
    (T : Raw.{0} I K) (hc : ConvexOn ℝ univ (P.price T)) :
    SublinearPrice ((tangentPlane P).price T) := by
  rw [funext (tangentPlane_price_eq_directionalPrice P T hc)]
  exact sublinearPrice_directionalPrice hc (P.collapsed T 0)

end

end FiniteFourier
end LinearAlgebra
end OAI
