import OAI.Computability.BorderVNP.CrossingFusionEnergy
import OAI.Computability.BorderVNP.CrossingRate

/-!
# The width of the fused cut

The ceiling in the number of base-`2^m` ports accounts for the entire cut,
including the sequence of mode labels and the occupation state at energy
`D H`. The proof bounds the mode overhead while allowing the number of
directions to grow with the wire width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter
open scoped Topology

/-- Number of base-`2^m` ports used for the padded cut index on PDF page 12. -/
noncomputable def bridgePorts (m d : ℕ) : ℕ :=
  ⌈((d : ℝ) * Real.logb 2 (2 * (leastEnergy m : ℝ)) +
    Real.logb 2 (stateCountAt (d * leastEnergy m))) / m⌉₊

private theorem mode_overhead :
    Tendsto (fun m : ℕ => Real.logb 2 (2 * (leastEnergy m:ℝ)) / Real.sqrt m) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => (leastEnergy m:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).mpr leastEnergy_atTop
  have hp := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).tendsto_div_nhds_zero.comp ht
  have hpl := hp.div_const (Real.log 2)
  rw [zero_div] at hpl
  have hroot (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  have hu : Tendsto (fun m : ℕ => 1 / Real.sqrt (Real.sqrt (leastEnergy m))) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp ht))
  have hv := leastEnergy_sqrt_rate.sqrt
  have hz := (hu.add hpl).mul hv
  simp only [zero_add, zero_mul] at hz
  apply hz.congr fun m => ?_
  have hH : (0:ℝ) < leastEnergy m := by exact_mod_cast (leastEnergy_spec m).1
  have hhs : Real.sqrt (Real.sqrt (leastEnergy m:ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hH)).ne'
  simp only [Function.comp_apply, Real.sqrt_div (Real.sqrt_nonneg _),
    Real.logb, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne']
  rw [← hroot _ hH.le]
  field_simp

/-- The encoded cut has asymptotically one square root of the direction
count in ports. This also allows any diverging number of directions
eventually bounded by the bit width. -/
theorem bridgePorts_limit {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    (hsub : ∀ᶠ m : ℕ in atTop, D m ≤ m) :
    Tendsto (fun m : ℕ => (bridgePorts m (D m) : ℝ) / Real.sqrt (D m)) atTop (𝓝 1) := by
  have hprod := hD.atTop_mul_atTop leastEnergy_atTop
  have hcount := (stateCountAt_limit.comp hprod).mul leastEnergy_sqrt_rate
  rw [mul_inv_cancel₀ countExponent_pos.ne'] at hcount
  have hstate : Tendsto (fun m : ℕ =>
      Real.logb 2 (stateCountAt (D m * leastEnergy m)) / m / Real.sqrt (D m)) atTop (𝓝 1) := by
    apply hcount.congr'
    filter_upwards [hD.eventually_gt_atTop 0] with m hd
    have hH : (0:ℝ) < leastEnergy m := by exact_mod_cast (leastEnergy_spec m).1
    have hs := (Real.sqrt_pos.mpr hH).ne'
    simp only [Function.comp_apply, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    field_simp
  have hmode : Tendsto (fun m : ℕ =>
      D m * Real.logb 2 (2 * (leastEnergy m:ℝ)) / m / Real.sqrt (D m)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ mode_overhead
    · filter_upwards with m
      have h1 : 1 ≤ 2 * (leastEnergy m : ℝ) := by exact_mod_cast
        (show 1 ≤ 2 * leastEnergy m by have := (leastEnergy_spec m).1; omega)
      positivity [Real.logb_nonneg (by norm_num : (1:ℝ) < 2) h1]
    · filter_upwards [hsub, hD.eventually_gt_atTop 0] with m hm hd
      have hd' : 0 < (D m : ℝ) := by exact_mod_cast hd
      have hm' : 0 < (m:ℝ) := by exact_mod_cast (hd.trans_le hm)
      have hle := Real.sqrt_le_sqrt (show (D m:ℝ) ≤ m by exact_mod_cast hm)
      have h1 : 1 ≤ 2 * (leastEnergy m : ℝ) := by exact_mod_cast
        (show 1 ≤ 2 * leastEnergy m by have := (leastEnergy_spec m).1; omega)
      have hl := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) h1
      have hs := Real.sqrt_pos.mpr hd'
      have hmpos := Real.sqrt_pos.mpr hm'
      rw [div_le_div_iff₀ hs hmpos, div_mul_eq_mul_div, div_le_iff₀ hm']
      have h := mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg hs.le hmpos.le) hl)
      nlinarith only [h,
        Real.sq_sqrt hd'.le, Real.sq_sqrt hm'.le,
        congrArg (fun x => x * Real.logb 2 (2*(leastEnergy m:ℝ)) * Real.sqrt m)
          (Real.sq_sqrt hd'.le),
        congrArg (fun x => x * Real.logb 2 (2*(leastEnergy m:ℝ)) * Real.sqrt (D m))
          (Real.sq_sqrt hm'.le)]
  let raw (m : ℕ) := (D m * Real.logb 2 (2 * (leastEnergy m:ℝ)) +
    Real.logb 2 (stateCountAt (D m * leastEnergy m))) / m
  have hraw : Tendsto (fun m => raw m / Real.sqrt (D m)) atTop (𝓝 1) := by
    simpa only [raw, add_div, zero_add] using hmode.add hstate
  have hinv : Tendsto (fun m : ℕ => 1 / Real.sqrt (D m)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_iff (R := ℝ)).mpr hD))
  have hupper := hraw.add hinv
  rw [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hraw hupper
  · filter_upwards with m
    exact div_le_div_of_nonneg_right (Nat.le_ceil (raw m)) (Real.sqrt_nonneg _)
  · filter_upwards [hraw.eventually_const_lt (by norm_num : (0:ℝ) < 1)] with m hm
    change _ ≤ raw m / _ + 1 / _
    rw [← add_div]
    have hp : 0 ≤ raw m := by
      by_contra! h
      exact hm.not_ge (div_nonpos_of_nonpos_of_nonneg h.le (Real.sqrt_nonneg _))
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hp).le (Real.sqrt_nonneg _)

/-- The fused cut at `D = ⌊c₀ √m⌋` meets the numerical hypothesis used to
move a junction in §4.4. -/
theorem bridgePorts_eventual {c₀ : ℝ} (hc : 0 < c₀) :
    ∀ᶠ m : ℕ in atTop, (bridgePorts m (directions c₀ m):ℝ) ≤
      21/20 * Real.sqrt (directions c₀ m) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd : Tendsto (directions c₀) atTop atTop := tendsto_nat_floor_atTop.comp (hs.const_mul_atTop hc)
  have hm : ∀ᶠ m : ℕ in atTop, directions c₀ m ≤ m := by
    filter_upwards [hs.eventually_ge_atTop c₀] with m h
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      (directions c₀ m:ℝ) ≤ c₀ * Real.sqrt m := Nat.floor_le (mul_nonneg hc.le (Real.sqrt_nonneg _))
      _ ≤ _ := by simpa only [Function.comp_apply, Real.mul_self_sqrt (Nat.cast_nonneg m)] using
        mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (m:ℝ))
  filter_upwards [(bridgePorts_limit hd hm).eventually_lt_const (by norm_num : (1:ℝ) < 21/20),
    hd.eventually_gt_atTop 0] with m h hpos
  exact ((div_lt_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).mp h).le

end Crossing

end BorderVNP
end Computability
end OAI
