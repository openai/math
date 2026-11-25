import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! # Reciprocal differences of a monotone quadratic phase

On each interval between successive integer frequencies the real part of
`(1 - exp (2πit))⁻¹` is constant and its imaginary part is decreasing.
These properties control the total variation in summation by parts.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace Chirp

open Real

def phase (t : ℝ) : ℂ := Complex.exp ((2 * π * t : ℝ) * Complex.I)

def weight (t : ℝ) : ℂ := (1 - phase t)⁻¹

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_periodic : Function.Periodic phase 1 := by
  intro t
  unfold phase
  push_cast
  rw [show 2 * (π : ℂ) * ((t : ℂ) + 1) * Complex.I =
    2 * π * t * Complex.I + 2 * π * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem weight_periodic : Function.Periodic weight 1 := by
  intro t
  simp only [weight, phase_periodic t]

theorem norm_one_sub_phase {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖1 - phase t‖ = 2 * sin (π * t) := by
  have hs := sin_nonneg_of_nonneg_of_le_pi (mul_nonneg pi_pos.le ht.1)
    (show π * t ≤ π by simpa using mul_le_mul_of_nonneg_left ht.2 pi_pos.le)
  rw [norm_sub_rev, phase, mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * π * t / 2 = π * t by ring, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem sin_angle_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < sin (π * t) :=
  sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht.1)
    (by simpa using mul_lt_mul_of_pos_left ht.2 pi_pos)

theorem phase_ne_one {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : phase t ≠ 1 := by
  intro heq
  have h := norm_one_sub_phase ⟨ht.1.le, ht.2.le⟩
  rw [heq, sub_self, norm_zero] at h
  linarith [sin_angle_pos ht]

theorem weight_re {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : (weight t).re = 1 / 2 := by
  have hs := (sin_angle_pos ht).ne'
  rw [weight, Complex.inv_re, Complex.sub_re, Complex.one_re, Complex.normSq_eq_norm_sq,
    norm_one_sub_phase ⟨ht.1.le, ht.2.le⟩, phase, Complex.exp_ofReal_mul_I_re,
    mul_assoc 2 π t, cos_two_mul_eq_one_sub]
  field_simp
  ring

theorem weight_im {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (weight t).im = cos (π * t) / (2 * sin (π * t)) := by
  have hs := (sin_angle_pos ht).ne'
  rw [weight, Complex.inv_im, Complex.sub_im, Complex.one_im, Complex.normSq_eq_norm_sq,
    norm_one_sub_phase ⟨ht.1.le, ht.2.le⟩, phase, Complex.exp_ofReal_mul_I_im,
    mul_assoc 2 π t, sin_two_mul]
  field_simp
  ring

theorem weight_im_antitone : AntitoneOn (fun t => (weight t).im) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  change (weight y).im ≤ (weight x).im
  rw [weight_im hx, weight_im hy, div_le_div_iff₀ (mul_pos two_pos (sin_angle_pos hy))
    (mul_pos two_pos (sin_angle_pos hx))]
  have hdiff := sin_nonneg_of_nonneg_of_le_pi
    (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hxy pi_pos.le))
    (show π * y - π * x ≤ π by
      have h := mul_lt_mul_of_pos_left hy.2 pi_pos
      nlinarith [mul_nonneg pi_pos.le hx.1.le])
  rw [sin_sub] at hdiff
  linarith

/-- The quantitative denominator bound on a good interval of increments. -/
theorem norm_weight_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1-δ)) :
    ‖weight t‖ ≤ 1 / (4 * δ) := by
  have htl : 0 < t := lt_of_lt_of_le hδ ht.1
  have htu : t < 1 := lt_of_le_of_lt ht.2 (by linarith)
  have hs (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) : 2 * u ≤ sin (π * u) := by
    have h := mul_le_sin (mul_nonneg pi_pos.le hu)
      (show π * u ≤ π / 2 by linarith [mul_le_mul_of_nonneg_left hu' pi_pos.le])
    rwa [show 2 / π * (π * u) = 2 * u by field_simp] at h
  have hst : 2 * δ ≤ sin (π * t) := by
    by_cases h : t ≤ 1 / 2
    · linarith [hs t htl.le h, ht.1]
    · have hh := hs (1-t) (by linarith) (by linarith)
      rw [show π * (1-t) = π - π*t by ring, sin_pi_sub] at hh
      linarith [ht.2]
  rw [weight, norm_inv, norm_one_sub_phase ⟨htl.le, htu.le⟩, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

end Chirp

end

end NearSquareRoot
end Computability
end OAI
