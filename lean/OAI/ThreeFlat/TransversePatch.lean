import OAI.LinearAlgebra.SpectralBooks.PricePlanePatch

namespace OAI
/-! # A third Euclidean dimension from a transverse distance gradient

When distance to an apex has gradient of norm strictly below one, its tangent
direction has positive height over the planar patch. The convex hull of the
tangent plane and point contains a neighborhood in Euclidean three-space.
-/

namespace ThreeFlat

open Filter Set HyperbolicObstruction LinearAlgebra.SpectralBooks WithLp
open scoped Topology

private noncomputable def threeFlatOfPlaneApex {F : Type*} [Field F] {a : Book.Lift ℝ} {H : ℝ}
    (hH : 0 < H) (P : SpectralPlacementPrices F (flatApexHull a H)) :
    SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3)) := by
  let c : Book.Lift (Book.Lift ℝ) := toLp 2 (a, H / 2)
  have hc : c.snd ∈ Ioo (0 : ℝ) H :=
    ⟨by change 0 < H / 2; linarith, by change H / 2 < H; linarith⟩
  have hU : flatApexHull a H ∈ 𝓝 c :=
    mem_of_superset
      ((show Continuous (fun q : Book.Lift (Book.Lift ℝ) ↦ q.snd) from
        WithLp.continuous_snd ..).continuousAt (Ioo_mem_nhds hc.1 hc.2))
      (fun q hq ↦ mem_flatApexHull_of_height a hH q hq)
  let e (x : EuclideanSpace ℝ (Fin 3)) : Book.Lift (Book.Lift ℝ) :=
    toLp 2 (toLp 2 (x 0, x 1), x 2)
  have he : Isometry e := by
    apply Isometry.of_dist_eq
    intro x y
    rw [WithLp.prod_dist_eq_of_L2, EuclideanSpace.dist_eq, Fin.sum_univ_three]
    change Real.sqrt (dist (toLp 2 (x 0, x 1)) (toLp 2 (y 0, y 1)) ^ 2 +
      dist (x 2) (y 2) ^ 2) = _
    rw [WithLp.prod_dist_eq_of_L2, Real.sq_sqrt (by positivity)]
    rfl
  exact (P.ofNeighborhood hU).pullback e he

/-- A positive-distance apex whose distance gradient has norm below one on a
spectral planar patch produces prices on Euclidean three-space. -/
theorem threeFlat_of_planarPatch {F X : Type*} [Field F] [MetricSpace X]
    (P : SpectralPlacementPrices F X) (hX : CATZero X)
    {U : Set (Book.Lift ℝ)} {c : Book.Lift ℝ → X} {y g : Book.Lift ℝ} {z : X}
    (hc : ∀ s ∈ U, ∀ u ∈ U, dist (c s) (c u) = dist s u)
    (hy : U ∈ 𝓝 y) (hz : 0 < dist (c y) z)
    (hg : HasGradientAt (fun s ↦ dist (c s) z) g y) (hsmall : ‖g‖ < 1) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))) := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let s (n : ℕ) : ℝ := 1 / (n + 1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  obtain ⟨_, Q, _⟩ := Book.exists_tangentHull_spectralPrices ω hs hc hy hX z
    (M := 1) zero_le_one (Ultrafilter.of_le _) tendsto_one_div_add_atTop_nhds_zero_nat P hg
  apply Nonempty.intro (threeFlatOfPlaneApex (P := Q) ?_)
  change 0 < (1 : ℝ) * (dist (c y) z * Real.sqrt (1 - ‖g‖ ^ 2))
  rw [one_mul]
  have hprod := mul_pos (sub_pos.mpr hsmall) (show 0 < 1 + ‖g‖ by positivity)
  exact mul_pos hz (Real.sqrt_pos.mpr (by nlinarith only [hprod]))

end ThreeFlat

end OAI
