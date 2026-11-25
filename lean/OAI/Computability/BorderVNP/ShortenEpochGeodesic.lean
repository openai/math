import OAI.Computability.BorderVNP.ShortenEpochPlacement

/-!
# Actual oriented geodesic segments in the hyperbolic host

Every endpoint pair determines a geodesic with its midpoint as origin and
oppositely oriented ends. This file proves the assertion in the upper
half-plane using spatial hyperboloid coordinates. Equal radial distances
and equality in the triangle inequality force the two spatial vectors
to be negatives of each other.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Real UpperHalfPlane

/-- Affine orientation-preserving isometry sending the standard point to `c`. -/
noncomputable def shiftFactor (c z : UpperHalfPlane) : UpperHalfPlane :=
  c.re +ᵥ ((⟨c.im, c.im_pos⟩ : {y : ℝ // 0 < y}) • z)

/-- Inverse affine isometry from the local frame at `c` to the standard frame. -/
noncomputable def unshiftFactor (c z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨⟨(z.re - c.re) / c.im, z.im / c.im⟩, div_pos z.im_pos c.im_pos⟩

/-- Translation to the representative center is an isometry in one factor. -/
theorem shiftFactor_isometry (c : UpperHalfPlane) : Isometry (shiftFactor c) :=
  (isometry_real_vadd c.re).comp (isometry_pos_mul ⟨c.im,c.im_pos⟩)

/-- The inverse affine placement recovers every upper-half-plane point. -/
theorem shiftFactor_unshift (c z : UpperHalfPlane) : shiftFactor c (unshiftFactor c z) = z := by
  apply ext_re_im
  · rw [shiftFactor, vadd_re, pos_real_re]
    change c.re + c.im * ((z.re-c.re) / c.im) = z.re
    field_simp; ring
  · rw [shiftFactor, vadd_im, pos_real_im]
    change c.im * (z.im / c.im) = z.im
    field_simp

/-- The shifted hyperboloid origin is the specified center. -/
theorem shiftFactor_chart_origin (c : UpperHalfPlane) : shiftFactor c (tangentChart 0) = c := by
  apply ext_re_im <;> simp [shiftFactor, tangentChart, timeCoord, vadd_re, pos_real_re, vadd_im, pos_real_im]

/-- Recover the spatial coordinates of an arbitrary upper-half-plane point. -/
noncomputable def spatialCoords (z : UpperHalfPlane) : ℂ :=
  ⟨z.re / z.im, (z.re^2 + z.im^2 - 1) / (2*z.im)⟩

/-- The spatial chart covers the full upper half-plane. -/
theorem tangentChart_spatialCoords (z : UpperHalfPlane) : tangentChart (spatialCoords z) = z := by
  let x := z.re
  let y := z.im
  have hy : 0 < y := z.im_pos
  have htime : timeCoord (spatialCoords z) = (x^2+y^2+1)/(2*y) := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
    change √(1 + (x / y)^2 + ((x^2+y^2-1)/(2*y))^2)^2 = _
    rw [sq_sqrt (by positivity)]
    field_simp; ring
  have hd : timeCoord (spatialCoords z) - (spatialCoords z).im = 1/y := by
    rw [htime]; change _ - (x^2+y^2-1)/(2*y) = _; field_simp; ring
  apply ext_re_im
  · change (x/y) / (timeCoord (spatialCoords z) - (spatialCoords z).im) = x
    rw [hd]; field_simp
  · change 1 / (timeCoord (spatialCoords z) - (spatialCoords z).im) = y
    rw [hd, one_div_one_div]

private theorem tangentChart_radial (v : ℂ) :
    tangentLine (unitDirection v) (arsinh ‖v‖) = tangentChart v := by
  rw [tangentLine, sinh_arsinh, norm_smul_unitDirection]

private theorem factor_dist_radius (v : ℂ) :
    dist (tangentChart 0) (tangentChart v) = arsinh ‖v‖ := by
  have h := dist_tangentLine (unitDirection v) (unitDirection_norm _) 0 (arsinh ‖v‖)
  rw [tangentChart_radial, show tangentLine (unitDirection v) 0 = tangentChart 0 by simp [tangentLine]] at h
  simpa [abs_of_nonneg (arsinh_nonneg_iff.mpr (norm_nonneg v))] using h

private theorem factor_midpoint (a b : UpperHalfPlane) :
    ∃ c, dist c a = dist a b / 2 ∧ dist c b = dist a b / 2 := by
  let v := spatialCoords (unshiftFactor a b)
  let u := unitDirection v
  let r := arsinh ‖v‖
  have hr : 0 ≤ r := arsinh_nonneg_iff.mpr (norm_nonneg _)
  have ha : shiftFactor a (tangentLine u 0) = a := by simpa [tangentLine] using shiftFactor_chart_origin a
  have hb : shiftFactor a (tangentLine u r) = b := by
    rw [show tangentLine u r = tangentChart v from tangentChart_radial v]
    rw [show tangentChart v = unshiftFactor a b from tangentChart_spatialCoords _, shiftFactor_unshift]
  have hi : Isometry (fun t => shiftFactor a (tangentLine u t)) :=
    (shiftFactor_isometry a).comp (Isometry.of_dist_eq (fun x y => dist_tangentLine u (unitDirection_norm v) x y))
  have hd : dist a b = r := by rw [← ha, ← hb, hi.dist_eq 0 r, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hr]
  refine ⟨shiftFactor a (tangentLine u (r/2)), ?_, ?_⟩
  · rw [hd]
    calc
      _ = dist (shiftFactor a (tangentLine u (r/2))) (shiftFactor a (tangentLine u 0)) := by rw [ha]
      _ = _ := by rw [hi.dist_eq (r/2) 0,Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  · rw [hd,← hb,hi.dist_eq (r/2) r,Real.dist_eq,abs_of_nonpos (by linarith)]; ring

private theorem antipodal_of_radial_dist {v w : ℂ} {s : ℝ}
    (hv : dist (tangentChart 0) (tangentChart v) = s)
    (hw : dist (tangentChart 0) (tangentChart w) = s)
    (hvw : dist (tangentChart v) (tangentChart w) = 2*s) : v = -w := by
  have ht (x : ℂ) (h : dist (tangentChart 0) (tangentChart x) = s) : timeCoord x = cosh s := by
    rw [← h, cosh_dist_tangentChart]
    simp [timeCoord]
  have hdot := cosh_dist_tangentChart v w
  rw [hvw, ht v hv, ht w hw, cosh_two_mul, cosh_sq'] at hdot
  have hs (x : ℂ) (h : dist (tangentChart 0) (tangentChart x) = s) :
      x.re ^ 2 + x.im ^ 2 = sinh s ^ 2 := by
    rw [factor_dist_radius] at h
    rw [← h, sinh_arsinh, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsum : (v.re+w.re)^2 + (v.im+w.im)^2 = 0 := by
    nlinarith only [hs v hv, hs w hw, hdot, cosh_sq' s]
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im]
  · nlinarith only [hsum, sq_nonneg (v.im+w.im)]
  · nlinarith only [hsum, sq_nonneg (v.re+w.re)]

/-- Any oriented factor segment has opposite endpoints on one unit-speed
geodesic through a common midpoint. This includes the zero-length case. -/
theorem exists_factor_midpoint_line (a b : UpperHalfPlane) :
    ∃ (c : UpperHalfPlane) (u : ℂ), ‖u‖ = 1 ∧
      shiftFactor c (tangentLine u (-(dist a b / 2))) = a ∧
      shiftFactor c (tangentLine u (dist a b / 2)) = b := by
  obtain ⟨c,ha,hb⟩ := factor_midpoint a b
  let v := spatialCoords (unshiftFactor c a)
  let w := spatialCoords (unshiftFactor c b)
  have hva : shiftFactor c (tangentChart v) = a := by dsimp only [v]; rw [tangentChart_spatialCoords,shiftFactor_unshift]
  have hwb : shiftFactor c (tangentChart w) = b := by dsimp only [w]; rw [tangentChart_spatialCoords,shiftFactor_unshift]
  have hv : dist (tangentChart 0) (tangentChart v) = dist a b / 2 := by
    rw [← (shiftFactor_isometry c).dist_eq,shiftFactor_chart_origin,hva,ha]
  have hw : dist (tangentChart 0) (tangentChart w) = dist a b / 2 := by
    rw [← (shiftFactor_isometry c).dist_eq,shiftFactor_chart_origin,hwb,hb]
  have hvw : dist (tangentChart v) (tangentChart w) = 2*(dist a b / 2) := by
    rw [← (shiftFactor_isometry c).dist_eq, hva, hwb]; ring
  have hanti := antipodal_of_radial_dist hv hw hvw
  rw [factor_dist_radius] at hw
  refine ⟨c, unitDirection w,unitDirection_norm _,?_,?_⟩
  · rw [← hw, tangentLine, sinh_neg, sinh_arsinh, _root_.neg_smul, norm_smul_unitDirection, ← hanti, hva]
  · rw [← hw, tangentChart_radial, hwb]

end Epoch

end BorderVNP
end Computability
end OAI
