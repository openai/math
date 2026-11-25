import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace OAI
/-! # The three-dimensional Student profile

On the normalized load interval `[0,1]` the profile increases from zero to
one half. Its inverse at one third determines the square exponent bound.
-/

namespace ThreeFlat

open Set

/-- The contribution of a site whose load is a fraction `t` of the total price. -/
noncomputable def profile (t : ℝ) : ℝ :=
  (Real.arcsin (Real.sqrt t) - Real.sqrt (t * (1 - t))) / Real.pi

theorem continuous_profile : Continuous profile := by
  unfold profile
  exact ((Real.continuous_arcsin.comp Real.continuous_sqrt).sub
    (Real.continuous_sqrt.comp (continuous_id.mul (continuous_const.sub continuous_id)))).div_const _

@[simp] theorem profile_zero : profile 0 = 0 := by simp [profile]

@[simp] theorem profile_one : profile 1 = 1 / 2 := by
  simp only [profile, Real.sqrt_one, Real.arcsin_one, sub_self, mul_zero, Real.sqrt_zero,
    sub_zero]
  field_simp [Real.pi_ne_zero]

theorem hasDerivAt_profile {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt profile (t / (Real.pi * Real.sqrt t * Real.sqrt (1 - t))) t := by
  have h₀ : 0 < t := ht.1
  have h₁ : 0 < 1 - t := sub_pos.mpr ht.2
  have hs : Real.sqrt t < 1 := by
    have := Real.sq_sqrt h₀.le
    nlinarith [Real.sqrt_nonneg t, ht.2]
  have hn : Real.sqrt t ≠ -1 := by linarith [Real.sqrt_nonneg t]
  have ha := (Real.hasDerivAt_arcsin hn hs.ne).comp t
    (Real.hasDerivAt_sqrt h₀.ne')
  have hb := (Real.hasDerivAt_sqrt (mul_pos h₀ h₁).ne').comp t
    ((hasDerivAt_id t).mul ((hasDerivAt_id t).const_sub 1))
  have hd : HasDerivAt profile _ t := (ha.sub hb).div_const Real.pi
  convert hd using 1
  rw [Real.sq_sqrt h₀.le, Real.sqrt_mul h₀.le]
  dsimp
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 h₀).ne', (Real.sqrt_pos.2 h₁).ne']
  ring

theorem strictMonoOn_profile : StrictMonoOn profile (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_profile.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_profile ht).deriv]
  exact div_pos ht.1 (mul_pos (mul_pos Real.pi_pos (Real.sqrt_pos.2 ht.1))
    (Real.sqrt_pos.2 (sub_pos.mpr ht.2)))

theorem exists_profile_eq {p : ℝ} (hp : p ∈ Icc 0 (1 / 2)) :
    ∃ t ∈ Icc 0 1, profile t = p := by
  refine intermediate_value_Icc (f := profile) zero_le_one continuous_profile.continuousOn ?_
  simpa using hp

/-- The inverse of the profile on its range `[0,1/2]`, extended by zero. -/
noncomputable def profileInv (p : ℝ) : ℝ :=
  open Classical in
  if hp : p ∈ Icc 0 (1 / 2) then Classical.choose (exists_profile_eq hp) else 0

theorem profileInv_mem {p : ℝ} (hp : p ∈ Icc 0 (1 / 2)) : profileInv p ∈ Icc 0 1 := by
  simpa only [profileInv, dite_eq_left hp] using (Classical.choose_spec (exists_profile_eq hp)).1

theorem profile_profileInv {p : ℝ} (hp : p ∈ Icc 0 (1 / 2)) : profile (profileInv p) = p := by
  simpa only [profileInv, dite_eq_left hp] using (Classical.choose_spec (exists_profile_eq hp)).2

theorem profileInv_profile {t : ℝ} (ht : t ∈ Icc 0 1) : profileInv (profile t) = t := by
  have hp : profile t ∈ Icc 0 (1 / 2) := by
    constructor
    · simpa using strictMonoOn_profile.monotoneOn (left_mem_Icc.mpr zero_le_one) ht ht.1
    · simpa using strictMonoOn_profile.monotoneOn ht (right_mem_Icc.mpr zero_le_one) ht.2
  exact strictMonoOn_profile.injOn (profileInv_mem hp) ht (profile_profileInv hp)

private theorem oneThird_mem : (1 / 3 : ℝ) ∈ Icc 0 (1 / 2) := by
  constructor <;> norm_num

@[simp] theorem profile_profileInv_oneThird : profile (profileInv (1 / 3)) = 1 / 3 :=
  profile_profileInv oneThird_mem

theorem profileInv_oneThird_pos : 0 < profileInv (1 / 3) := by
  apply lt_of_le_of_ne (profileInv_mem oneThird_mem).1
  intro h
  have he := profile_profileInv_oneThird
  rw [← h, profile_zero] at he
  norm_num at he

theorem profileInv_oneThird_lt_one : profileInv (1 / 3) < 1 := by
  apply lt_of_le_of_ne (profileInv_mem oneThird_mem).2
  intro h
  have he := profile_profileInv_oneThird
  rw [h, profile_one] at he
  norm_num at he

/-- The three-flat lower bound on the square exponent, `2 / P⁻¹(1/3)`. -/
noncomputable def omegaThree : ℝ := 2 / profileInv (1 / 3)

theorem omegaThree_le_of_profile {L : ℝ} (hL : 2 ≤ L) (hP : profile (2 / L) ≤ 1 / 3) :
    omegaThree ≤ L := by
  have pos : 0 < L := by linarith
  have ht : 2 / L ∈ Icc 0 1 :=
    ⟨by positivity, (div_le_one pos).mpr hL⟩
  have h := (strictMonoOn_profile.le_iff_le ht (profileInv_mem oneThird_mem)).mp
    (by simpa only [profile_profileInv_oneThird] using hP)
  apply (div_le_iff₀ profileInv_oneThird_pos).2
  simpa [mul_comm] using (div_le_iff₀ pos).1 h

theorem omegaThree_ge_of_profile {t : ℝ} (ht : t ∈ Ioo 0 1) (h : 1 / 3 ≤ profile t) :
    2 / t ≤ omegaThree := by
  have hle := (strictMonoOn_profile.le_iff_le (profileInv_mem oneThird_mem)
    (show t ∈ Icc 0 1 from ⟨ht.1.le, ht.2.le⟩)).mp (by simpa only [profile_profileInv_oneThird] using h)
  exact div_le_div_of_nonneg_left (by norm_num) profileInv_oneThird_pos hle

end ThreeFlat

end OAI
