import OAI.LinearAlgebra.SpectralBooks.Book.BookBlowup
import OAI.LinearAlgebra.SpectralBooks.BookComparison
import OAI.LinearAlgebra.SpectralBooks.BookFlatHull
import OAI.LinearAlgebra.SpectralBooks.Book.BookTangent

/-!
# The tangent flat and the point on the other page in the metric ultralimit

In the pointed ultralimit with distances divided by `hₙ`, the points with
coordinates `y + hₙ v` realize a whole Euclidean flat. The points at fraction
`hₙ M` on the geodesic toward `x` realize the point `b_M` in `eq:book-tangent`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Book

open HyperbolicObstruction Filter Set
open scoped Topology RealInnerProductSpace

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
  {U : Set E} {φ : E → X} (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
  {y : E} (hy : U ∈ 𝓝 y)

/-- The bounded representative of a page direction, using the center until
the coordinates are inside the patch. -/
noncomputable def pageSection (v : E) : BlowupSection ω hs (φ y) := by
  classical
  refine ⟨fun n ↦ ⟨if y + s n • v ∈ U then φ (y + s n • v) else φ y⟩, ‖v‖, fun n ↦ ?_⟩
  rw [MetricScale.dist_eq]
  dsimp only
  split_ifs with hn
  · rw [hφ y (mem_of_mem_nhds hy) _ hn, dist_comm, dist_eq_norm]
    simp [norm_smul, Real.norm_of_nonneg (hs n).le, (hs n).ne']
  · simp

/-- The page coordinates in the pointed ultralimit. -/
noncomputable def tangentFlat (v : E) : Blowup ω hs (φ y) :=
  MetricLimit.point (pageSection ω hs hφ hy v)

variable (hX : CATZero X) (x : X) {M : ℝ} (hM : 0 ≤ M)

/-- The bounded representative on the segment to the fixed ambient point. -/
noncomputable def raySection : BlowupSection ω hs (φ y) := by
  classical
  refine ⟨fun n ↦ ⟨if s n * M ≤ 1 then CATZero.segment hX (φ y) x (s n * M) else φ y⟩,
    M * dist (φ y) x, fun n ↦ ?_⟩
  rw [MetricScale.dist_eq]
  dsimp only
  split_ifs with hn
  · rw [CATZero.segment_left hX (φ y) x ⟨mul_nonneg (hs n).le hM, hn⟩]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (hs n).ne', one_mul]
  · simpa using mul_nonneg hM (dist_nonneg (x := φ y) (y := x))

/-- The manuscript's `b_M` in the metric ultralimit. -/
noncomputable def tangentRayPoint : Blowup ω hs (φ y) :=
  MetricLimit.point (raySection ω hs hX x hM)

variable (hω : (ω : Filter ℕ) ≤ atTop) (h₀ : Tendsto s atTop (𝓝 0))

include hy h₀ in
private theorem eventually_in_patch (v : E) : ∀ᶠ n in atTop, y + s n • v ∈ U := by
  have hlim : Tendsto (fun n ↦ y + s n • v) atTop (𝓝 y) := by
    simpa using (h₀.smul_const v).const_add y
  exact hlim hy

include h₀ in
/-- The representative of a fixed flat direction eventually has the manuscript's
unclamped coordinates. -/
theorem eventually_pageSection (v : E) :
    ∀ᶠ n in atTop, ((pageSection ω hs hφ hy v).val n).val = φ (y + s n • v) := by
  classical
  filter_upwards [eventually_in_patch hy h₀ v] with n hn
  simp [pageSection, hn]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
include h₀ in
/-- The apex representative eventually equals the point at fraction `s n * M`
on the original geodesic. -/
theorem eventually_raySection :
    ∀ᶠ n in atTop, ((raySection (φ := φ) (y := y) ω hs hX x hM).val n).val =
      CATZero.segment hX (φ y) x (s n * M) := by
  classical
  have hscale : Tendsto (fun n ↦ s n * M) atTop (𝓝 0) := by simpa using h₀.mul_const M
  filter_upwards [hscale.eventually_lt_const zero_lt_one] with n hn
  simp [raySection, hn.le]

include h₀ hM in
/-- For a corner of the original patch, its contracted displacement in the
blow-up is represented by the same fractional geodesic construction used for
the apex. This identifies the two descriptions of the sites `A_{h,M}`. -/
theorem eventually_pageSection_segment {z : E} (hz : z ∈ U) :
    ∀ᶠ n in atTop, ((pageSection ω hs hφ hy (M • (z - y))).val n).val =
      CATZero.segment hX (φ y) (φ z) (s n * M) := by
  have hscale : Tendsto (fun n ↦ s n * M) atTop (𝓝 0) := by simpa using h₀.mul_const M
  filter_upwards [eventually_pageSection ω hs hφ hy h₀ (M • (z - y)),
    eventually_in_patch hy h₀ (M • (z - y)), hscale.eventually_lt_const zero_lt_one]
    with n he hin hn
  rw [he]
  let t := s n * M
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg (hs n).le hM, hn.le⟩
  have hcoord : y + s n • M • (z - y) = AffineMap.lineMap y z t := by
    rw [smul_smul, AffineMap.lineMap_apply_module', add_comm]
  apply CATZero.eq_segment_of_dist hX ht
  · rw [hφ y (mem_of_mem_nhds hy) _ hin, hφ y (mem_of_mem_nhds hy) z hz, hcoord,
      dist_left_lineMap, Real.norm_of_nonneg ht.1]
  · rw [hφ _ hin z hz, hφ y (mem_of_mem_nhds hy) z hz, hcoord, dist_comm, dist_right_lineMap,
      Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]

include hω h₀ in
/-- The rescaled page gives an isometric copy of the entire Euclidean space. -/
theorem isometry_tangentFlat : Isometry (tangentFlat ω hs hφ hy) := by
  classical
  apply Isometry.of_dist_eq
  intro v w
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist _ _)
  apply (tendsto_const_nhds (x := dist v w)).congr'
  filter_upwards [hω (eventually_in_patch hy h₀ v), hω (eventually_in_patch hy h₀ w)]
    with n hv hw
  rw [MetricScale.dist_eq]
  dsimp only [pageSection]
  rw [ite_eq_left hv, ite_eq_left hw, hφ _ hv _ hw, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (hs n).le, ← mul_assoc,
    inv_mul_cancel₀ (hs n).ne', one_mul]

include hω h₀ in
/-- Equation `eq:book-tangent` in the actual pointed metric ultralimit. -/
theorem tangentRayPoint_dist_tangentFlat [CompleteSpace E] {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) :
    dist (tangentRayPoint (φ := φ) (y := y) ω hs hX x hM) (tangentFlat ω hs hφ hy v) =
      dist (M • liftedDirection g (dist (φ y) x)) (horizontal v) := by
  classical
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist _ _)
  have hpos : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h₀, Eventually.of_forall hs⟩
  have ht := (tendsto_tangent_dist hX hφ hy x hg v hM).comp (hpos.mono_left hω)
  apply ht.congr'
  have hscale : Tendsto (fun n ↦ s n * M) atTop (𝓝 0) := by simpa using h₀.mul_const M
  filter_upwards [hω (eventually_in_patch hy h₀ v), hω (hscale.eventually_lt_const zero_lt_one)]
    with n hv hn
  rw [MetricScale.dist_eq]
  dsimp only [pageSection, raySection, Function.comp_apply]
  rw [ite_eq_left hv, ite_eq_left hn.le, div_eq_inv_mul]

include hω h₀ in
/-- The convex hull of the full flat and the Euclidean point `MX` embeds
isometrically in the rescaled ultralimit, taking the marked sites to their
actual bounded representatives. -/
theorem exists_tangentHull_isometry [CompleteSpace E] {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) :
    let A := M • liftedDirection g (dist (φ y) x)
    ∃ F : flatApexHull A.fst A.snd → Blowup ω hs (φ y), Isometry F ∧
      (∀ v, F ⟨horizontal v, flatApexHull_base_mem _ _ v⟩ = tangentFlat ω hs hφ hy v) ∧
      F ⟨A, flatApexHull_apex_mem _ _⟩ = tangentRayPoint (φ := φ) (y := y) ω hs hX x hM := by
  let A := M • liftedDirection g (dist (φ y) x)
  refine cat0_flatApexHull_isometry (isCAT0_of_catZero (blowup_catZero hX ω hs (φ y)))
    (isometry_tangentFlat ω hs hφ hy hω h₀) _ A.fst A.snd ?_ ?_
  · change 0 ≤ M * (dist (φ y) x * Real.sqrt (1 - ‖g‖ ^ 2))
    positivity
  · intro v
    rw [tangentRayPoint_dist_tangentFlat ω hs hφ hy hX x hM hω h₀ hg v]
    change dist A (horizontal v) ^ 2 = _
    rw [WithLp.prod_dist_eq_of_L2, Real.sq_sqrt (by positivity)]
    simp [horizontal]

include hω h₀ in
/-- Spectral prices on the Euclidean convex hull of the tangent flat and `MX`.
They compute the limits of the original placed tensor prices for any bounded
representatives of the marked sites. -/
theorem exists_tangentHull_spectralPrices [CompleteSpace E] {K : Type*} [Field K]
    (P : SpectralPlacementPrices K X) {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) :
    let A := M • liftedDirection g (dist (φ y) x)
    ∃ (F : flatApexHull A.fst A.snd → Blowup ω hs (φ y))
      (Q : SpectralPlacementPrices K (flatApexHull A.fst A.snd)), Isometry F ∧
      (∀ v, F ⟨horizontal v, flatApexHull_base_mem _ _ v⟩ = tangentFlat ω hs hφ hy v) ∧
      F ⟨A, flatApexHull_apex_mem _ _⟩ = tangentRayPoint (φ := φ) (y := y) ω hs hX x hM ∧
      ∀ {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I K) (p : I → flatApexHull A.fst A.snd)
        (z : I → BlowupSection ω hs (φ y)), (∀ i, MetricLimit.point (z i) = F (p i)) →
        Tendsto (fun n ↦ P.price T (fun i ↦ ((z i).val n).val) / s n) (ω : Filter ℕ)
          (𝓝 (Q.price T p)) := by
  obtain ⟨F, hF, hb, ha⟩ := exists_tangentHull_isometry ω hs hφ hy hX x hM hω h₀ hg
  refine ⟨F, (blowupSpectralPrices ω hs (φ y) P).pullback F hF, hF, hb, ha, ?_⟩
  intro I _ T p z hz
  have h := tendsto_blowupSpectralPrices ω hs (φ y) P T z
  rwa [show MetricLimit.point ∘ z = F ∘ p from funext hz] at h

end Book

end SpectralBooks
end LinearAlgebra
end OAI
