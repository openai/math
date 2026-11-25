import OAI.Computability.BorderVNP.ShortenEpochTangent
import OAI.Computability.BorderVNP.ShortenEpochBoundary

/-!
# Turning hyperbolic bisectors into finite geodesic sides

A hyperbolic bisector in the half-plane is vertical or a Euclidean
semicircle centered on the real axis. Both have explicit unit-speed
parametrizations. On a compact lifted tile the inverse parameter is
bounded, so only a finite-length portion of each line is needed in
the boundary strip estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Real Set Metric

private theorem bounded_parameter {K : Set UpperHalfPlane} (hK : IsCompact K)
    (t : UpperHalfPlane → ℝ) (ht : Continuous t) :
    ∃ T ≥ 0, ∀ z ∈ K, |t z| ≤ T := by
  obtain ⟨T,hT⟩ := (isBounded_iff_subset_closedBall (0 : ℝ)).mp (hK.image ht).isBounded
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  intro z hz
  have hh := hT (mem_image_of_mem t hz)
  exact (show |t z| ≤ T by simpa [mem_closedBall, Real.dist_eq] using hh).trans (le_max_left _ _)

private theorem bounded_arc {K : Set UpperHalfPlane} (hK : IsCompact K)
    {Γ : ℝ → UpperHalfPlane} (hΓ : Isometry Γ)
    (t : UpperHalfPlane → ℝ) (ht : Continuous t) (bisector : Set UpperHalfPlane)
    (h : ∀ z ∈ bisector, Γ (t z) = z) :
    ∃ L ≥ 0, ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ z ∈ K ∩ bisector, ∃ s ∈ Icc (0 : ℝ) L, γ s = z := by
  obtain ⟨T,hT,hbound⟩ := bounded_parameter hK t ht
  let γ (s : ℝ) := Γ (s-T)
  refine ⟨2*T, by positivity, γ, Isometry.of_dist_eq (fun x y => ?_), ?_⟩
  · simp only [γ, hΓ.dist_eq, Real.dist_eq]
    congr 1
    ring
  · intro z hz
    obtain ⟨ha,hb⟩ := abs_le.mp (hbound z hz.1)
    exact ⟨t z+T, ⟨by linarith, by linarith⟩, by simp [γ, h z hz.2]⟩

/-- The compact part of any vertical bisector lies on a bounded unit-speed side. -/
theorem vertical_bounded_arc {K : Set UpperHalfPlane} (hK : IsCompact K) (a : ℝ) :
    ∃ L ≥ 0, ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ z ∈ K, z.re = a → ∃ s ∈ Icc (0 : ℝ) L, γ s = z := by
  let Γ (t : ℝ) := UpperHalfPlane.mk ⟨a, Real.exp t⟩ (exp_pos t)
  let t (z : UpperHalfPlane) := log z.im
  have hΓ : Isometry Γ := UpperHalfPlane.isometry_vertical_line _
  have ht : Continuous t := UpperHalfPlane.continuous_im.log (fun z => z.im_ne_zero)
  obtain ⟨L,hL,γ,hi,h⟩ := bounded_arc hK hΓ t ht {z | z.re = a}
    (fun z hz => UpperHalfPlane.ext_re_im hz.symm (Real.exp_log z.im_pos))
  exact ⟨L,hL,γ,hi,fun z hz he => h z ⟨hz,he⟩⟩

/-- The spatial x-axis of the hyperboloid maps to the Euclidean unit
semicircle, at unit hyperbolic speed. -/
private theorem unit_semicircle (t : ℝ) :
    (tangentLine 1 t).re = Real.sinh t / Real.cosh t ∧
    (tangentLine 1 t).im = 1 / Real.cosh t := by
  have hv : Real.sinh t • (1 : ℂ) = ((Real.sinh t : ℝ) : ℂ) := by
    rw [Complex.real_smul, mul_one]
  have h : timeCoord (((Real.sinh t : ℝ) : ℂ)) = cosh t := by
    rw [timeCoord, Complex.ofReal_re, Complex.ofReal_im, zero_pow two_ne_zero, add_zero,
      ← Real.cosh_sq', Real.sqrt_sq (cosh_pos _).le]
  change ((Real.sinh t • (1:ℂ)).re / (timeCoord _ - (Real.sinh t • (1:ℂ)).im) = _) ∧
    (1 / (timeCoord _ - (Real.sinh t • (1:ℂ)).im) = _)
  rw [hv, h, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  exact ⟨rfl,rfl⟩

/-- The compact part of any Euclidean semicircle centered on the real axis
lies on a bounded unit-speed hyperbolic side. -/
theorem semicircle_bounded_arc {K : Set UpperHalfPlane} (hK : IsCompact K)
    (a R : ℝ) (hR : 0 < R) :
    ∃ L ≥ 0, ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ z ∈ K, (z.re-a)^2 + z.im^2 = R^2 →
        ∃ s ∈ Icc (0 : ℝ) L, γ s = z := by
  let Γ (t : ℝ) := a +ᵥ ((⟨R,hR⟩ : {r : ℝ // 0 < r}) • tangentLine 1 t)
  let t (z : UpperHalfPlane) := Real.arsinh ((z.re-a)/z.im)
  have hg : Isometry (tangentLine 1) :=
    Isometry.of_dist_eq fun u v => dist_tangentLine _ (by simp) u v
  have hΓ : Isometry Γ :=
    (UpperHalfPlane.isometry_real_vadd a).comp ((UpperHalfPlane.isometry_pos_mul _).comp hg)
  have ht : Continuous t := Real.continuous_arsinh.comp
    ((UpperHalfPlane.continuous_re.sub continuous_const).div UpperHalfPlane.continuous_im
      (fun z => z.im_ne_zero))
  have he (z : UpperHalfPlane) (hz : (z.re-a)^2 + z.im^2 = R^2) : Γ (t z) = z := by
    have hc : Real.cosh (t z) = R / z.im := by
      dsimp [t]
      rw [cosh_arsinh]
      apply (sq_eq_sq₀ (sqrt_nonneg _) (div_pos hR z.im_pos).le).mp
      rw [sq_sqrt (by positivity)]
      field_simp
      linarith only [hz]
    have hs : Real.sinh (t z) = (z.re-a)/z.im := by simp [t]
    apply UpperHalfPlane.ext_re_im
    · simp only [Γ, UpperHalfPlane.vadd_re, UpperHalfPlane.pos_real_re, (unit_semicircle (t z)).1, hc, hs]
      field_simp
      ring
    · simp only [Γ, UpperHalfPlane.vadd_im, UpperHalfPlane.pos_real_im, (unit_semicircle (t z)).2, hc]
      field_simp
  obtain ⟨L,hL,γ,hi,h⟩ := bounded_arc hK hΓ t ht {z | (z.re-a)^2 + z.im^2 = R^2} he
  exact ⟨L,hL,γ,hi,fun z hz e => h z ⟨hz,e⟩⟩

end Epoch

end BorderVNP
end Computability
end OAI
