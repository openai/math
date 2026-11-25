import OAI.ThreeFlat.TransversePatch
import OAI.ThreeFlat.ProductGradient
import OAI.ThreeFlat.TransverseSlope

namespace OAI
/-! # A transverse four-point defect in a parallel set

In a spectral parallel set with product distance, an interior non-unit slope in
the transverse factor provides an apex of positive height over a two-dimensional
tangent plane. Magnification at an interior point of the hull yields a three-flat.
-/

namespace ThreeFlat

open Filter Set HyperbolicObstruction LinearAlgebra.SpectralBooks WithLp
open scoped Topology

/-- A non-tree transverse factor of an isometrically split parallel set in a
spectral CAT(0) space gives a spectral Euclidean three-flat. The splitting is
expressed as the distance formula for its coordinate map. -/
theorem spectralThreeFlat_of_transverse_fourPointDefect {F X Y : Type*}
    [Field F] [MetricSpace X] [MetricSpace Y]
    (P : SpectralPlacementPrices F X) (hX : CATZero X) (hY : CATZero Y)
    (e : ℝ → Y → X)
    (he : ∀ s t : ℝ, ∀ u v : Y, dist (e s u) (e t v) =
      Real.sqrt (dist s t ^ 2 + dist u v ^ 2))
    (a b z w : Y)
    (hbad : max (dist a z + dist b w) (dist a w + dist b z) < dist a b + dist z w) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨L, c, v, y, hc, hy, hfy, hdiff, hd⟩ :=
    exists_segment_nonunit_slope_of_fourPointDefect hY a b z w hbad
  let f (s : ℝ) := dist (c s) v
  let o : Book.Lift ℝ := toLp 2 (0, y)
  let g : Book.Lift ℝ := toLp 2 (0, deriv f y)
  let U : Set (Book.Lift ℝ) := {p | p.snd ∈ Icc 0 L}
  let φ (p : Book.Lift ℝ) := e p.fst (c p.snd)
  have hφ : ∀ p ∈ U, ∀ q ∈ U, dist (φ p) (φ q) = dist p q := by
    intro p hp q hq
    dsimp only [φ]
    rw [he, hc _ hp _ hq, WithLp.prod_dist_eq_of_L2]
  have hU : U ∈ 𝓝 o :=
    (show Continuous (fun q : Book.Lift ℝ ↦ q.snd) from WithLp.continuous_snd ..).continuousAt
      (Icc_mem_nhds hy.1 hy.2)
  have hgrad : HasGradientAt (fun p ↦ dist (φ p) (e 0 v)) g o := by
    simpa only [φ, he, Real.dist_eq, sub_zero, sq_abs, f, g, o] using
      (hasGradientAt_sqrt_sum_sq (f := f) (y := y) hfy hdiff)
  have hgo : ‖g‖ < 1 := by
    simpa only [g, WithLp.norm_toLp_snd, Real.norm_eq_abs, f] using hd
  have hdist : 0 < dist (φ o) (e 0 v) := by
    simpa [φ, o, he, Real.sqrt_sq (dist_nonneg (x := c y) (y := v))] using hfy
  exact threeFlat_of_planarPatch P hX hφ hU hdist hgrad hgo

end ThreeFlat

end OAI
