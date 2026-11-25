import OAI.Computability.VPVNP.StateCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The least energy budget of a fresh wire

Section 4.2 chooses the first positive `H` with `Q(H) > 2H · 2^m`.
Taking logarithms at this budget and at its predecessor gives the exact
leading constant even though the least budget need not be a smooth function.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter VPVNP.Crossing
open scoped Topology

/-- The manuscript's count uses half-integral energies. -/
abbrev stateCountAt (H : ℕ) : ℕ := cutoffCount (2*H)

/-- Growth constant in the manuscript's original, undoubled energy units. -/
noncomputable def countExponent : ℝ := stateExponent * Real.sqrt 2

/-- Equation (4.1), in base two and the original energy units. -/
theorem stateCountAt_limit :
    Tendsto (fun H : ℕ => Real.logb 2 (stateCountAt H) / Real.sqrt H)
      atTop (𝓝 countExponent) := by
  have hh : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  apply ((cutoffCount_limit.comp hh).mul_const (Real.sqrt 2)).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  unfold stateCountAt
  field_simp

/-- The constant in the state-count asymptotic is strictly positive. -/
theorem countExponent_pos : 0 < countExponent := mul_pos stateExponent_pos (by positivity)

private theorem logb_over_sqrt :
    Tendsto (fun n : ℕ => Real.logb 2 n / Real.sqrt n) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).div_const (Real.log 2)
  rw [zero_div] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Real.logb, Real.sqrt_eq_rpow]
  ring

private noncomputable def netBits (H : ℕ) : ℝ :=
  Real.logb 2 (stateCountAt H) - Real.logb 2 (2*(H:ℝ))

private theorem netBits_rate :
    Tendsto (fun H : ℕ => netBits H / Real.sqrt H) atTop (𝓝 countExponent) := by
  have hinv : Tendsto (fun n : ℕ => (1:ℝ) / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have lim := stateCountAt_limit.sub (hinv.add logb_over_sqrt)
  simp only [zero_add, sub_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with H hH
  have hpos : (H:ℝ) ≠ 0 := by positivity
  simp only [netBits, Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hpos, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),
    sub_div, add_div]

private theorem log_cost (H m : ℕ) (hH : 0 < H) :
    Real.logb 2 ((2*H*2^m : ℕ) : ℝ) = Real.logb 2 (2*(H:ℝ)) + m := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat,
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

private theorem budget_iff (H m : ℕ) (hH : 0 < H) :
    2*H*2^m < stateCountAt H ↔ (m:ℝ) < netBits H := by
  rw [netBits, lt_sub_iff_add_lt, add_comm, ← log_cost H m hH]
  have h₁ : (0:ℝ) < ((2*H*2^m:ℕ):ℝ) := by positivity
  have h₂ : (0:ℝ) < (stateCountAt H:ℝ) := by exact_mod_cast cutoffCount_pos _
  constructor
  · intro h
    exact Real.logb_lt_logb (by norm_num) h₁ (by exact_mod_cast h)
  · intro h
    by_contra! h'
    exact h.not_ge (Real.logb_le_logb_of_le (by norm_num) h₂ (by exact_mod_cast h'))

private theorem exists_budget (m : ℕ) :
    ∃ H : ℕ, 0 < H ∧ 2*H*2^m < stateCountAt H := by
  have lim := netBits_rate.pos_mul_atTop countExponent_pos
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  obtain ⟨H,hH,h⟩ := ((eventually_gt_atTop (0:ℕ)).and (lim.eventually_gt_atTop (m:ℝ))).exists
  have hs : Real.sqrt (H:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hH)).ne'
  exact ⟨H,hH,(budget_iff H m hH).2 (by simpa only [div_mul_cancel₀ _ hs, Function.comp_apply] using h)⟩

/-- Least positive energy cutoff allowing a fresh `m`-bit wire to cross. -/
noncomputable def leastEnergy (m : ℕ) : ℕ := Nat.find (exists_budget m)

/-- The selected cutoff admits the integral crossing at every incoming energy. -/
theorem leastEnergy_spec (m : ℕ) :
    0 < leastEnergy m ∧ 2 * leastEnergy m * 2^m < stateCountAt (leastEnergy m) :=
  Nat.find_spec (exists_budget m)

private theorem count_mono : Monotone stateCountAt := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_mono
    omega
  · intros
    positivity

/-- The least budget diverges with the number of bits in the wire. -/
theorem leastEnergy_atTop : Tendsto leastEnergy atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (stateCountAt b)] with m hm
  by_contra! h
  obtain ⟨hp, hc⟩ := leastEnergy_spec m
  have h1 := count_mono h.le
  have h2 := Nat.lt_two_pow_self (n := m)
  have h3 : 2^m ≤ 2 * leastEnergy m * 2^m := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Adjacent budgets sandwich the wire bits between two copies of the same
state-count asymptotic. Equivalently `H ∼ (m / c)^2`. -/
theorem leastEnergy_sqrt_rate :
    Tendsto (fun m : ℕ => Real.sqrt (leastEnergy m) / m) atTop (𝓝 countExponent⁻¹) := by
  have predTop := (tendsto_sub_atTop_nat 1).comp leastEnergy_atTop
  have hre : Tendsto (fun m : ℕ => (1:ℝ) / (leastEnergy m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_iff (R := ℝ)).mpr leastEnergy_atTop)
  have hratio : Tendsto (fun m : ℕ =>
      Real.sqrt ((leastEnergy m - 1 : ℕ):ℝ) / Real.sqrt (leastEnergy m)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub hre
    simp only [sub_zero] at h
    have hs := h.sqrt
    rw [Real.sqrt_one] at hs
    apply hs.congr fun n => ?_
    have hn := (leastEnergy_spec n).1
    rw [← Real.sqrt_div (Nat.cast_nonneg _), Nat.cast_sub hn, Nat.cast_one]
    congr 1
    have hn' : (leastEnergy n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hu := netBits_rate.comp leastEnergy_atTop
  have hl := (netBits_rate.comp predTop).mul hratio
  rw [mul_one] at hl
  have sandwich : Tendsto (fun m : ℕ => m / Real.sqrt (leastEnergy m)) atTop (𝓝 countExponent) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    · filter_upwards [leastEnergy_atTop.eventually_ge_atTop 2] with m hm
      have hn : 0 < leastEnergy m - 1 := by omega
      have no := Nat.find_min (exists_budget m) (show leastEnergy m - 1 < leastEnergy m by omega)
      have hle : netBits (leastEnergy m - 1) ≤ m :=
        le_of_not_gt (fun h => no ⟨hn, (budget_iff _ _ hn).2 h⟩)
      simp only [Function.comp_apply]
      have hden := (Real.sqrt_pos.mpr (show (0:ℝ) < ((leastEnergy m - 1:ℕ):ℝ) by exact_mod_cast hn)).ne'
      rw [div_mul_div_cancel₀ hden]
      exact div_le_div_of_nonneg_right hle (Real.sqrt_nonneg _)
    · filter_upwards with m
      obtain ⟨hp,hc⟩ := leastEnergy_spec m
      exact div_le_div_of_nonneg_right ((budget_iff _ _ hp).1 hc).le (Real.sqrt_nonneg _)
  simpa only [inv_div] using sandwich.inv₀ countExponent_pos.ne'

end Crossing

end BorderVNP
end Computability
end OAI
