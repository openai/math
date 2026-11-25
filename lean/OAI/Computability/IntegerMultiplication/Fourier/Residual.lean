import OAI.Computability.IntegerMultiplication.Fourier.Coefficient

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real

/-- Real inequalities controlling weight drop. -/
private theorem separation {s t x delta m : ℝ} (hs : 0≤s) (ht : s≤t)
    (hb : |delta|≤s/2) (hm : |x| = m) (h : 1≤m) :
    t*m*(t*m-s) ≤ (delta-t*x)^2 - delta^2 := by
  have hu : |delta-t*x| ≥ t*m-|delta| := by
    have e := abs_add_le (t*x-delta) delta
    rw [sub_add_cancel,abs_mul,abs_of_nonneg (hs.trans ht),hm,abs_sub_comm] at e
    linarith
  have hp : s ≤ t*m := by nlinarith
  have : |delta|≤t*m := by linarith
  have hk : (t*m-|delta|)^2 ≤ (delta-t*x)^2 :=
    (pow_le_pow_left₀ (by linarith) hu 2).trans (sq_abs _).le
  have he := sq_abs delta
  nlinarith

private theorem all_separation {s t x delta g m : ℝ} (hs : 0≤s) (h : 1≤g)
    (ht : (1+1/g)*s≤t) (hm : |x|=m) (hk : 1≤m) (hδ : |delta|≤s/2) :
    s^2*m^2/g ≤ (delta-t*x)^2-delta^2 := by
  have hg : 0<g := by linarith
  have hn : 0≤ 1 / g*s := by positivity
  rw [add_mul,one_mul] at ht
  have he := separation hs (by linarith : s ≤ t) hδ hm hk
  have ha : (s/g)*m ≤ t*m - s := by
    have e := mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ m)
    rw [add_mul] at e
    have mono : s ≤ s * m := by nlinarith
    have : s/g=1/g*s := by ring
    rw [this]
    linarith
  have hb : s*m*((s/g)*m) ≤ t*m*(t*m-s) := by
    have hm' : 0≤m := by linarith
    have ht' : 0≤t := by linarith
    refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hm') ha ?_ (mul_nonneg ht' hm')
    exact mul_nonneg (div_nonneg hs hg.le) hm'
  rw [show s^2*m^2/g=s*m*((s/g)*m) by ring]
  exact hb.trans he

private theorem far_separation {s t x delta m : ℝ} (hs : 0≤s) (ht : s≤t)
    (hδ : |delta|≤s/2) (hm : |x|=m) (hk : 2≤m) :
    s^2*m^2/2 ≤ (delta-t*x)^2-delta^2 := by
  have hh := separation hs ht hδ hm (by linarith : 1≤m)
  have hu : s*m≤t*m := mul_le_mul_of_nonneg_right ht (by linarith)
  have he := mul_le_mul hu (show s*m/2≤t*m-s by nlinarith)
    (show 0≤s*m/2 by exact div_nonneg (mul_nonneg hs (by linarith)) (by linarith))
    (show 0≤t*m by exact mul_nonneg (hs.trans ht) (by linarith))
  linarith [show s^2*m^2/2=s*m*(s*m/2) by ring]

noncomputable def ratio (t D : ℕ) (delta j : ℤ) : ℝ :=
  coef D (delta-t*j) / coef D delta

@[simp] theorem ratio_nonneg (t D delta j) : 0≤ratio t D delta j := by
  exact div_nonneg (coef_nonneg ..) (coef_nonneg ..)

private theorem ratio_shift {s t D : ℕ} {delta j : ℤ} {q R : ℝ}
    (hδ : delta∈rad D) (_hR : 0≤R) (hD : R*(D:ℝ)≤(s:ℝ)^2)
    (hn : 0<D) (hq : 0≤q)
    (hs : q*(s:ℝ)^2 ≤ ((delta:ℝ)-(t:ℝ)*j)^2-(delta:ℝ)^2) :
    ratio t D delta j ≤ Real.exp (-(q*R)/2) := by
  have he : ((delta:ℝ))^2 ≤ (((delta-(t:ℤ)*j:ℤ):ℝ))^2 := by
    push_cast
    have hx : 0 ≤ q*(s:ℝ)^2 := mul_nonneg hq (sq_nonneg _)
    linarith
  have ha : ((delta:ℤ))^2 ≤ (delta-t*j)^2 := by exact_mod_cast he
  have hab : |delta| ≤ |delta- (t:ℤ)*j| := by
    by_contra! hz
    have h := (sq_lt_sq).mpr hz
    omega
  have h := coef_ratio_bound hab hδ
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hd : (0:ℝ)<D := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hD hq]

/-- Uniform bound from the gap. m=|j|. -/
theorem gap_ratio {s t D : ℕ} {delta j : ℤ} {g R : ℝ}
    (hg : 1≤g) (hδ : delta ∈ rad D)
    (ht : (1+1/g)*(s:ℝ)≤(t:ℝ))
    (hb : |(delta:ℝ)|≤(s:ℝ)/2)
    (hR : 0≤R) (hD : R*(D:ℝ)≤(s:ℝ)^2)
    (hn : 0<D) (hj : j≠0) :
    ratio t D delta j ≤ Real.exp (-((|(j:ℝ)|^2/g)*R)/2) := by
  apply ratio_shift hδ hR hD hn (div_nonneg (sq_nonneg _) (by linarith))
  rw [show |(j:ℝ)|^2/g*(s:ℝ)^2=(s:ℝ)^2*|(j:ℝ)|^2/g by ring]
  apply all_separation (by positivity) hg ht rfl _ hb
  exact_mod_cast (show (1:ℤ) ≤ |j| from (abs_pos.mpr hj))

/-- Quadratic suppression for residuals off the nearest neighbors. -/
theorem far_ratio {s t D : ℕ} {delta j : ℤ} {R : ℝ}
    (hδ : delta ∈ rad D) (ht : s≤t)
    (hb : |(delta:ℝ)|≤(s:ℝ)/2)
    (hR : 0≤R) (hD : R*(D:ℝ)≤(s:ℝ)^2)
    (hn : 0<D) (hj : 2≤|j|) :
    ratio t D delta j ≤ Real.exp (-(|(j:ℝ)|^2*R)/4) := by
  rw [show -(|(j:ℝ)|^2*R)/4= -((|(j:ℝ)|^2/2)*R)/2 by ring]
  apply ratio_shift hδ hR hD hn (by positivity)
  rw [show |(j:ℝ)|^2/2*(s:ℝ)^2=(s:ℝ)^2*|(j:ℝ)|^2/2 by ring]
  exact far_separation (by positivity) (by exact_mod_cast ht) hb rfl (by exact_mod_cast hj)

theorem int_gt_rad {x : ℤ} {i J : ℕ} (he : i ≤ J) (h : x ∉ rad J) :
    (i:ℤ) < |x| := by
  simp only [mem_rad,not_and_or] at h
  have := abs_le (a:=x) (b:=(i:ℤ))
  omega

/-- Weight bound for any tail index. Use this simply with the term count to suppress
the whole far tail, choosing J large enough (but still a small power of precision).
-/
theorem tail_ratio {s t D J : ℕ} {delta j : ℤ} {R : ℝ}
    (hδ : delta ∈ rad D) (ht : s≤t)
    (hb : |(delta:ℝ)|≤(s:ℝ)/2)
    (hR : 0≤R) (hD : R*(D:ℝ)≤(s:ℝ)^2)
    (hn : 0<D) (hJ : 1≤ J) (hj : j∉rad J) :
    ratio t D delta j ≤ Real.exp (-((J:ℝ)^2*R)/4) := by
  have e : (2:ℤ)≤|j| := int_gt_rad hJ hj -- 1< abs
  have hm := far_ratio hδ ht hb hR hD hn e
  refine hm.trans (Real.exp_le_exp.mpr ?_)
  have he := int_gt_rad (le_refl J) hj
  have hh : (J:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast he.le
  have : (J:ℝ)^2*R ≤ |(j:ℝ)|^2*R := by gcongr
  linarith

/-- Weight sum at the near neighbors (excluding the central), in a form allowing complex
or kernel truncation via domain subsets. -/
theorem near_ratio {s t D J : ℕ} {delta : ℤ} {g R : ℝ} (l : Finset ℤ)
    (hg : 1≤g) (hδ : delta ∈ rad D) (ht : (1+1/g)*(s:ℝ)≤(t:ℝ))
    (hb : |(delta:ℝ)|≤(s:ℝ)/2)
    (hR : 0≤R) (hD : R*(D:ℝ)≤(s:ℝ)^2)
    (hn : 0<D) (hj : l ⊆ rad J) (hz : (0:ℤ)∉l) :
    ∑ j ∈ l, ratio t D delta j ≤ (2*(J:ℝ)+1)*Real.exp (-((1/g)*R)/2) := by
  let b := Real.exp (-((1/g)*R)/2)
  have he : ∑ j ∈ l, ratio t D delta j ≤ ∑ _j ∈ l, b := by
    refine sum_le_sum fun j e => ?_
    have hh : j ≠ 0 := fun h => hz (h ▸ e)
    refine (gap_ratio hg hδ ht hb hR hD hn hh).trans (Real.exp_le_exp.mpr ?_)
    have hw : 1≤|(j:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |j| from (abs_pos.mpr hh))
    have hq : 1 / g * R ≤ |(j:ℝ)|^2/g * R := by
      rw [show (1:ℝ)/g=1^2/g by simp]
      gcongr
    linarith
  simp only [sum_const,nsmul_eq_mul] at he
  refine he.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hq := card_le_card hj
  rw [rad_card] at hq
  exact_mod_cast hq

/-- Reciprocal table bound. Require d-band width exponent R not too big and choose D within
a factor 2 of division by it. -/
theorem center_ratio_bound {s D : ℕ} {delta : ℤ} {R : ℝ}
    (ha : 4*|delta|≤(D:ℤ)) (hb : |(delta:ℝ)|≤(s:ℝ)/2)
    (_hR : 0≤R) (hD : (s:ℝ)^2≤2*R*D) (h : 0<D) :
    1/coef D delta ≤ (2*D+1)*Real.exp R := by
  have hδ : delta∈rad D := mem_rad.mpr (abs_le.mp (by linarith [abs_nonneg delta]))
  have hh := coef_lower ha
  have hd : 0 < (D:ℝ) := by exact_mod_cast h
  have he : Real.exp (-R)≤Real.exp (-(2*(delta:ℝ)^2)/D) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hd]
    have hb' := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hb'
    nlinarith
  have hq : (0:ℝ)<2*D+1 := by positivity
  rw [div_le_iff₀ hq] at hh
  rw [div_le_iff₀ (coef_pos hδ)]
  rw [Real.exp_neg] at he
  have hmul : Real.exp R * (Real.exp R)⁻¹ = 1 := by exact mul_inv_cancel₀ (Real.exp_pos _).ne'
  nlinarith [mul_le_mul_of_nonneg_left (he.trans hh) (Real.exp_pos R).le]

end Fourier

end IntegerMultiplication
end Computability
end OAI
