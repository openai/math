import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Placing tangent-plane configurations in the hyperbolic host

In spatial coordinates on the unit hyperboloid, the map from a Euclidean
plane to the hyperbolic plane is nonexpanding. A point at Euclidean radius
`s` lies at hyperbolic distance `arsinh s` along the prescribed unit-speed
geodesic. The difference is uniformly small relative to `s` at small
scales, and can be charged to the terminal hooks in Section 6.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open scoped UpperHalfPlane Topology
open Real Filter

/-- The time coordinate over a point in the spatial plane of the hyperboloid. -/
noncomputable def timeCoord (v : ℂ) : ℝ := Real.sqrt (1 + v.re ^ 2 + v.im ^ 2)

private theorem timeCoord_sq (v : ℂ) : timeCoord v ^ 2 = 1 + v.re ^ 2 + v.im ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem timeCoord_sub_im_pos (v : ℂ) : 0 < timeCoord v - v.im := by
  have h := timeCoord_sq v
  have ht : 0 ≤ timeCoord v := Real.sqrt_nonneg _
  by_contra! hle
  have hsq := pow_le_pow_left₀ ht (show timeCoord v ≤ v.im by linarith) 2
  nlinarith only [h, hsq, sq_nonneg v.re]

/-- Spatial hyperboloid coordinates, expressed in Mathlib's upper half-plane. -/
noncomputable def tangentChart (v : ℂ) : UpperHalfPlane :=
  ⟨⟨v.re / (timeCoord v - v.im), 1 / (timeCoord v - v.im)⟩,
    one_div_pos.mpr (timeCoord_sub_im_pos v)⟩

/-- Hyperbolic cosine distance in spatial hyperboloid coordinates. -/
theorem cosh_dist_tangentChart (v w : ℂ) :
    cosh (dist (tangentChart v) (tangentChart w)) =
      timeCoord v * timeCoord w - v.re * w.re - v.im * w.im := by
  let p := timeCoord v - v.im
  let q := timeCoord w - w.im
  have hp : p ≠ 0 := (timeCoord_sub_im_pos v).ne'
  have hq : q ≠ 0 := (timeCoord_sub_im_pos w).ne'
  have h1 : v.re ^ 2 + 1 = p * (timeCoord v + v.im) := by
    dsimp [p]; nlinarith only [timeCoord_sq v]
  have h2 : w.re ^ 2 + 1 = q * (timeCoord w + w.im) := by
    dsimp [q]; nlinarith only [timeCoord_sq w]
  rw [UpperHalfPlane.cosh_dist']
  change ((v.re / p - w.re / q)^2 + (1/p)^2 + (1/q)^2) /
      (2 * (1/p) * (1/q)) = _
  field_simp
  calc
    _ = (v.re^2 + 1) * q^2 + (w.re^2 + 1) * p^2 - 2 * v.re * w.re * p * q := by ring
    _ = _ := by rw [h1, h2]; dsimp [p, q]; ring

private theorem one_add_half_sq_le_cosh {s : ℝ} (hs : 0 ≤ s) :
    1 + s ^ 2 / 2 ≤ Real.cosh s := by
  have h := Real.self_le_sinh_iff.mpr (show 0 ≤ s / 2 by positivity)
  have hsinh := pow_le_pow_left₀ (show 0 ≤ s / 2 by positivity) h 2
  rw [show s = 2 * (s / 2) by ring, Real.cosh_two_mul, Real.cosh_sq']
  nlinarith only [hsinh]

/-- Sending any two gadget vertices to their hyperboloid lifts cannot increase
the length of their connecting wire. -/
theorem dist_tangentChart_le (v w : ℂ) : dist (tangentChart v) (tangentChart w) ≤ dist v w := by
  have h1 := one_add_half_sq_le_cosh (dist_nonneg (x := tangentChart v) (y := tangentChart w))
  rw [cosh_dist_tangentChart] at h1
  have h2 : dist v w ^ 2 = (v.re - w.re)^2 + (v.im - w.im)^2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
  nlinarith only [h1, h2, timeCoord_sq v, timeCoord_sq w,
    sq_nonneg (timeCoord v - timeCoord w), dist_nonneg (x := v) (y := w),
    dist_nonneg (x := tangentChart v) (y := tangentChart w)]

/-- The geodesic through the center in the spatial direction `u`. -/
noncomputable def tangentLine (u : ℂ) (s : ℝ) : UpperHalfPlane :=
  tangentChart (Real.sinh s • u)

private theorem timeCoord_smul (u : ℂ) (hu : ‖u‖ = 1) (s : ℝ) :
    timeCoord (Real.sinh s • u) = Real.cosh s := by
  have hnorm := Complex.sq_norm u
  rw [hu, Complex.normSq_apply] at hnorm
  have h := timeCoord_sq (Real.sinh s • u)
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h
  have hr : (u.re)^2 + (u.im)^2 = 1 := by nlinarith only [hnorm]
  rw [mul_pow, mul_pow, add_assoc 1, ← mul_add, hr, mul_one] at h
  have hpos : 0 ≤ timeCoord (Real.sinh s • u) := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ hpos (Real.cosh_pos _).le).mp (h.trans (Real.cosh_sq' s).symm)

/-- The whole signed radial line is a unit-speed geodesic for the upper
half-plane metric. Both orientations of a crossing use this same line. -/
theorem dist_tangentLine (u : ℂ) (hu : ‖u‖ = 1) (r s : ℝ) :
    dist (tangentLine u r) (tangentLine u s) = |r - s| := by
  have hnorm := Complex.sq_norm u
  rw [hu, Complex.normSq_apply] at hnorm
  have hr : u.re^2 + u.im^2 = 1 := by nlinarith only [hnorm]
  have hc : cosh (dist (tangentLine u r) (tangentLine u s)) = cosh (r - s) := by
    rw [tangentLine, tangentLine, cosh_dist_tangentChart, timeCoord_smul u hu,
      timeCoord_smul u hu, Real.cosh_sub]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    linear_combination -Real.sinh r * Real.sinh s * hr
  apply le_antisymm
  · simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc.le
  · simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc.ge

/-- A gadget terminal with Euclidean spatial radius `s` and the unit-speed
geodesic terminal of radius `s` are exactly this far apart. -/
theorem tangentChart_hook (u : ℂ) (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    dist (tangentChart (s • u)) (tangentLine u s) = s - Real.arsinh s := by
  have hle : Real.arsinh s ≤ s := by
    rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
    exact Real.self_le_sinh_iff.mpr hs
  rw [show tangentChart (s • u) = tangentLine u (Real.arsinh s) by simp [tangentLine],
    dist_tangentLine u hu, abs_of_nonpos (sub_nonpos.mpr hle)]
  ring

/-- Any prescribed relative terminal hook allowance works throughout a
sufficiently small ball, independently of the tangent direction. -/
theorem uniform_tangent_hooks {η : ℝ} (hη : 0 < η) :
    ∃ h > 0, ∀ s ∈ Set.Icc (0 : ℝ) h, ∀ u : ℂ, ‖u‖ = 1 →
      dist (tangentChart (s • u)) (tangentLine u s) ≤ η * s := by
  have hd : HasDerivAt (fun s : ℝ => s - Real.arsinh s) 0 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).sub (Real.hasDerivAt_arsinh 0)
    simpa [Pi.sub_def] using h
  have ht := hasDerivAt_iff_tendsto_slope.mp hd
  have hev := ht.eventually (gt_mem_nhds hη)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ/2, by positivity, ?_⟩
  intro s hs u hu
  rw [tangentChart_hook u hu hs.1]
  rcases eq_or_lt_of_le hs.1 with h | h
  · simp [← h]
  have hd' : dist s 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos h]; linarith [hs.2]
  have he' := he hd' (show s ∈ ({0} : Set ℝ)ᶜ by simpa using h.ne')
  simpa [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul] using
    (show (s - Real.arsinh s) / s ≤ η by simpa [slope, vsub_eq_sub, smul_eq_mul,
      div_eq_inv_mul] using he'.le) |> (fun hh => (div_le_iff₀ h).mp hh)

end Epoch

end BorderVNP
end Computability
end OAI
