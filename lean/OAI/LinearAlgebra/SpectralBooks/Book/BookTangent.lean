import OAI.Geometry.HyperbolicGroups.CATZero
import OAI.LinearAlgebra.SpectralBooks.Book.BookNormal
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Tangent distances from an isometric patch to an ambient geodesic

At a point where the distance to a fixed ambient point is differentiable in
flat coordinates, its gradient determines the distances between the rescaled
flat and the rescaled geodesic toward that point. This proves the limit in
`eq:book-tangent` using squared-distance comparison at the two opposite
directions of the flat.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Book

open Filter Set HyperbolicObstruction
open scoped Topology RealInnerProductSpace

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The derivative of the squared distance along a line, in difference quotient form. -/
private theorem sq_slope {f : E → ℝ} {y g : E} (hg : HasGradientAt f g y) (w : E) :
    Tendsto (fun h : ℝ ↦ (f (y + h • w) ^ 2 - f y ^ 2) / h)
      (𝓝[>] 0) (𝓝 (2 * f y * ⟪g, w⟫)) := by
  have hline : HasDerivAt (fun h : ℝ ↦ y + h • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hf := hg.hasFDerivAt
  have hcomp : HasDerivAt (fun h : ℝ ↦ f (y + h • w)) ⟪g,w⟫ 0 := by
    exact (show HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (y + (0 : ℝ) • w) by
      simpa using hf).comp_hasDerivAt 0 hline
  simpa [div_eq_inv_mul, mul_assoc] using (hcomp.pow 2).tendsto_slope_zero_right

/-- For `h ↓ 0`, the square of the rescaled distance from the point at
fraction `hM` on the geodesic to the point with flat coordinates `y + hv`
converges to the polarized Euclidean expression in `eq:book-tangent`. -/
theorem tendsto_tangent_dist_sq (hX : CATZero X) {U : Set E} {φ : E → X}
    (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X)
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun h : ℝ ↦ (dist (CATZero.segment hX (φ y) x (h * M))
      (φ (y + h • v)) / h) ^ 2) (𝓝[>] 0)
      (𝓝 (M ^ 2 * dist (φ y) x ^ 2 + ‖v‖ ^ 2 + 2 * M * dist (φ y) x * ⟪g, v⟫)) := by
  let f (z : E) := dist (φ z) x
  let P (h : ℝ) := CATZero.segment hX (φ y) x (h * M)
  let Z (w : E) (h : ℝ) := φ (y + h • w)
  let A (w : E) (h : ℝ) := (dist (P h) (Z w h) / h) ^ 2
  let B (w : E) (h : ℝ) := M ^ 2 * f y ^ 2 + (1 - h * M) * ‖w‖ ^ 2 +
    M * ((f (y + h • w) ^ 2 - f y ^ 2) / h)
  let L (w : E) := M ^ 2 * f y ^ 2 + ‖w‖ ^ 2 + 2 * M * f y * ⟪g,w⟫
  change Tendsto (A v) _ (𝓝 (L v))
  have hzero : Tendsto (fun h : ℝ ↦ h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hscale : Tendsto (fun h : ℝ ↦ h * M) (𝓝[>] 0) (𝓝 0) := by
    simpa using hzero.mul_const M
  have hpar : ∀ᶠ h : ℝ in 𝓝[>] 0, h * M ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, hscale.eventually_lt_const zero_lt_one]
      with h hh h₁
    exact ⟨mul_nonneg (le_of_lt hh) hM, h₁.le⟩
  have hin (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, y + h • w ∈ U := by
    have hlim : Tendsto (fun h : ℝ ↦ y + h • w) (𝓝[>] 0) (𝓝 y) := by
      simpa using (hzero.smul_const w).const_add y
    exact hlim hy
  have hdist (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, dist (Z w h) (φ y) = h * ‖w‖ := by
    filter_upwards [hin w, self_mem_nhdsWithin] with h hin' hh
    dsimp only [Z]
    rw [hφ _ hin' y (mem_of_mem_nhds hy), dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < h from hh)]
  have hupper (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, A w h ≤ B w h := by
    filter_upwards [hpar, hdist w, self_mem_nhdsWithin] with h hp hd hh
    have hc := CATZero.segment_cn hX (φ y) x (Z w h) hp
    rw [hd, dist_comm (Z w h)] at hc
    change dist (P h) (Z w h) ^ 2 ≤ _ at hc
    change (dist (P h) (Z w h) / h) ^ 2 ≤ _
    dsimp only [B, f]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos (show 0 < h from hh))]
    calc
      _ ≤ _ := hc
      _ = _ := by dsimp only [Z]; field_simp [(show 0 < h from hh).ne']; ring
  have hB (w : E) : Tendsto (B w) (𝓝[>] 0) (𝓝 (L w)) := by
    have hs := (sq_slope hg w).const_mul M
    have hl := (tendsto_const_nhds (x := M ^ 2 * f y ^ 2)).add
      (((tendsto_const_nhds (x := 1)).sub hscale).mul_const (‖w‖ ^ 2))
    convert! hl.add hs using 2
    dsimp [L, f]
    ring
  let D := M ^ 2 * f y ^ 2 + ‖v‖ ^ 2
  have hpair : ∀ᶠ h : ℝ in 𝓝[>] 0, 2 * D ≤ A v h + A (-v) h := by
    filter_upwards [hin v, hin (-v), hdist v, hdist (-v), hpar, self_mem_nhdsWithin]
      with h hv hn hd hd' hp hh
    have hh' : 0 < h := hh
    have hdiff : y + h • v - (y + h • -v) = (2 * h) • v := by
      rw [smul_neg, two_mul, add_smul]; abel
    have hspan : dist (Z v h) (Z (-v) h) = 2 * h * ‖v‖ := by
      dsimp only [Z]
      rw [hφ _ hv _ hn, dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [norm_neg] at hd'
    have hc := CATZero.cn_of_dist hX (x := Z v h) (y := Z (-v) h)
      (p := φ y) (P h) (t := 1 / 2) (by norm_num)
      (by rw [hd, hspan]; ring) (by rw [dist_comm, hd', hspan]; ring)
    rw [dist_comm (P h) (φ y), CATZero.segment_left hX (φ y) x hp, hspan] at hc
    dsimp only [D, A, f]
    rw [div_pow, div_pow, ← add_div, le_div_iff₀ (sq_pos_of_pos hh')]
    linarith only [hc]
  have hlower : ∀ᶠ h : ℝ in 𝓝[>] 0, 2 * D - B (-v) h ≤ A v h := by
    filter_upwards [hpair, hupper (-v)] with h hp hu
    linarith
  have hlowlim : Tendsto (fun h ↦ 2 * D - B (-v) h) (𝓝[>] 0) (𝓝 (L v)) := by
    have heq : 2 * D - L (-v) = L v := by
      dsimp [D, L]
      rw [norm_neg, inner_neg_right]
      ring
    rw [← heq]
    exact tendsto_const_nhds.sub (hB (-v))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim (hB v) hlower (hupper v)

/-- Rescaled distances converge to the actual Euclidean distance between the
lifted direction and the horizontal test point. -/
theorem tendsto_tangent_dist (hX : CATZero X) {U : Set E} {φ : E → X}
    (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X)
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun h : ℝ ↦ dist (CATZero.segment hX (φ y) x (h * M)) (φ (y + h • v)) / h)
      (𝓝[>] 0) (𝓝 (dist (M • liftedDirection g (dist (φ y) x)) (horizontal v))) := by
  have hlip : LipschitzOnWith 1 (fun u ↦ dist (φ u) x) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu z hz
    simpa [hφ u hu z hz] using dist_dist_dist_le_left (φ u) (φ z) x
  have hgnorm : ‖g‖ ≤ 1 := by simpa using hg.hasFDerivAt.le_of_lipschitzOn hy hlip
  have hs := tendsto_tangent_dist_sq hX hφ hy x hg v hM
  rw [← liftedDirection_dist_sq _ _ _ _ hgnorm] at hs
  have hr := hs.sqrt
  rw [Real.sqrt_sq dist_nonneg] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact Real.sqrt_sq (div_nonneg dist_nonneg (le_of_lt hh))

end Book

end SpectralBooks
end LinearAlgebra
end OAI
