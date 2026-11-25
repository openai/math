import OAI.Hierarchy.ProbeOuterRates
import OAI.Hierarchy.ProbeParameters

namespace OAI
/-! # The paper's dyadic cutoff and rational scheduled prices -/

namespace Hierarchy.AdaptiveProbe
noncomputable section

/-- For the printed cutoff t^8 the normalized cooling allowance is at most
one as soon as W≥9. All logarithms here are natural. -/
theorem dyadic_cooling_integral (W : ℕ) (wide : 9≤W) :
    let r := (dyadicScale W)^8
    0<r ∧ r≤1 ∧ (W:ℝ)⁻¹^2*(1-Real.log r)≤1 := by
  have wp : (0:ℝ)<W := by exact_mod_cast (by omega : 0<W)
  have large : (9:ℝ)≤W := by exact_mod_cast wide
  have small : dyadicScale W≤1 := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have pos : 0<dyadicScale W := by unfold dyadicScale; positivity
  refine ⟨pow_pos pos _,pow_le_one₀ pos.le small,?_⟩
  have logtwo : Real.log 2≤1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have form : Real.log (dyadicScale W ^ 8) = -(8*(W:ℝ)*Real.log 2) := by
    simp [dyadicScale,Real.log_pow,one_div,Real.log_inv]
   ; ring
  rw [form,inv_pow,inv_mul_eq_div]
  apply (div_le_iff₀ (pow_pos wp 2)).2
  have size : 8*(W:ℝ)*Real.log 2 ≤ 8*W := by
    exact (mul_le_mul_of_nonneg_left logtwo (by positivity : 0≤8*(W:ℝ))).trans_eq (mul_one _)
  nlinarith [mul_nonneg (sub_nonneg.mpr large) wp.le]

/-- The positive quadratic coefficient is fixed uniformly over all price
vectors in a box with squared mass at most R A² per payload. -/
theorem small_quadratic_price {W R A : ℝ} (hW : 0<W) (hR : 0≤R) :
    ∃ a : ℚ, 0<a ∧ (a:ℝ)*R*A^2≤W⁻¹^4 := by
  let D := R*A^2
  have nn : 0≤D := mul_nonneg hR (sq_nonneg A)
  have den : 0<D+1 := by linarith
  obtain ⟨a,pa,small⟩ := exists_rat_btwn (show (0:ℝ)<W⁻¹^4/(D+1) by positivity)
  refine ⟨a,by exact_mod_cast pa,?_⟩
  have h := (lt_div_iff₀ den).mp small
  change (a:ℝ)*R*A^2≤_
  dsimp [D] at h
  nlinarith

/-- A single rational cutoff and a single mesh serve every width and payload
count, given the per-payload score bound D and squared-gradient bound G. -/
theorem rational_outer_mesh (D V G a : ℝ) (ha : 0<a) :
    ∃ (s₀ : ℚ) (m : ℕ), 0<s₀ ∧ s₀≤1 ∧ (s₀:ℝ)*D<1 ∧ 0<m ∧
      V≤a*m ∧ G≤(s₀:ℝ)*a*m := by
  have nn : 0≤max 0 D := le_max_left ..
  have den : 0<max 0 D+1 := by linarith
  obtain ⟨s,hs,lim⟩ := exists_rat_btwn (lt_min zero_lt_one (one_div_pos.mpr den))
  have ss := lt_of_lt_of_le lim (min_le_left ..)
  have rate := (lt_div_iff₀ den).mp (lt_of_lt_of_le lim (min_le_right ..))
  obtain ⟨m,hm,hV,hG⟩ := choose_outer_mesh ha hs V G
  refine ⟨s,m,by exact_mod_cast hs,by exact_mod_cast ss.le,?_,hm,hV,hG⟩
  have step := mul_le_mul_of_nonneg_left (le_max_right 0 D) hs.le
  linarith

/-- Therefore every time at which the native local test is requested is
rational, including the two phase endpoints. -/
theorem clockTime_rat (s₀ : ℚ) (m j : ℕ) :
    clockTime (s₀:ℝ) m j = ((1-(j:ℚ)/m*(1-s₀):ℚ):ℝ) := by simp [clockTime]

/-- Below the printed time cutoff, even the maximal possible signed readings
stay beneath the truncated barrier. Here T=t² exactly. -/
theorem dyadic_small_time (k W : ℕ) (wide : 2*k+1≤W) :
    let t := dyadicScale W
    (W:ℝ)⁻¹^4*(1+2*(k:ℝ)/(t^2)^2)*t^8≤(W:ℝ)⁻¹^2 := by
  let t := dyadicScale W
  have ht : 0<t := by dsimp [t,dyadicScale]; positivity
  have cap : t≤1 := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have oneW : (1:ℝ)≤W := by exact_mod_cast (by omega : 1≤W)
  have dim : 1+2*(k:ℝ)≤W := by exact_mod_cast (by omega : 1+2*k≤W)
  have wp : (0:ℝ)<W := zero_lt_one.trans_le oneW
  have estimate : (1+2*(k:ℝ)/(t^2)^2)*t^8≤(W:ℝ)^2 := calc
    _ = t^8+2*(k:ℝ)*t^4 := by field_simp
    _ ≤ 1+2*(k:ℝ) := by
      have e : t^8≤1 := pow_le_one₀ ht.le cap
      have f := mul_le_mul_of_nonneg_left (show t^4≤1 from pow_le_one₀ ht.le cap)
        (by positivity : 0≤2*(k:ℝ))
      linarith
    _ ≤ _ := by nlinarith [mul_nonneg wp.le (sub_nonneg.mpr oneW)]
  change (W:ℝ)⁻¹^4*(1+2*(k:ℝ)/(t^2)^2)*t^8≤(W:ℝ)⁻¹^2
  calc
    _ ≤ (W:ℝ)⁻¹^4*(W:ℝ)^2 := by rw [mul_assoc]; gcongr
    _ = _ := by field_simp

/-- The resolution η used by the chain purchase test also makes the actual
payload-path error small when the chosen scale has NT≤1/4. -/
theorem payload_resolution (N k : ℕ) (hk : 0<k) {T : ℝ}
    (hT : 0≤T) (cap : T≤1) (tiles : N*T≤1/4) :
    let η := T/(100*k)
    η+N*(Real.sqrt (2*k)*η)+N*T≤1/2 := by
  have kOne : (1:ℝ)≤k := by exact_mod_cast hk
  have kp : (0:ℝ)<k := zero_lt_one.trans_le kOne
  have sqrtBound : Real.sqrt (2*(k:ℝ))≤2*k := by
    have sq := Real.sq_sqrt (by positivity : 0≤2*(k:ℝ))
    have mono := mul_nonneg (show 0≤2*(k:ℝ)-1 by linarith) (by positivity : 0≤2*(k:ℝ))
    nlinarith [Real.sqrt_nonneg (2*(k:ℝ))]
  have small : T/(100*(k:ℝ))≤1/100 := by
    apply (div_le_iff₀ (by positivity)).2; linarith
  have prod : Real.sqrt (2*(k:ℝ))*(T/(100*k))≤T/50 := calc
    _ ≤ 2*k*(T/(100*k)) := mul_le_mul_of_nonneg_right sqrtBound (by positivity)
    _ = _ := by field_simp; ring
  have summed := mul_le_mul_of_nonneg_left prod (Nat.cast_nonneg (α:=ℝ) N)
  dsimp only
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
