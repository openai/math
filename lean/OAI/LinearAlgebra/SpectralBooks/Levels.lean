import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # Adjacent exterior dimensions

Choosing the integer degree nearest from below to `(Q+1)/(1+Q^s)`, with
the top endpoint clamped to `Q-1`, controls both successive binomial ratios.
The resulting bounds are uniform in the prescribed exponent `s ∈ [-1,1]`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real

private theorem interior_floor {Q : ℕ} (hQ : 2 ≤ Q) {x : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ Q) :
    ∃ b : ℕ, b + 2 ≤ Q ∧ (b : ℝ) + 1 ≤ x ∧ x ≤ (b : ℝ) + 2 := by
  by_cases htop : ⌊x⌋₊ < Q
  · have hb := (Nat.one_le_floor_iff x).mpr h₁
    obtain ⟨b, hb'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ⌊x⌋₊ ≠ 0)
    refine ⟨b, by omega, ?_, ?_⟩
    · simpa [hb'] using Nat.floor_le (by linarith : 0 ≤ x)
    · have := Nat.lt_floor_add_one x
      rw [hb', Nat.cast_succ] at this
      linarith
  · have hb : Q - 2 + 2 = Q := by omega
    refine ⟨Q - 2, hb.le, ?_, ?_⟩
    · have hx := Nat.floor_le (by linarith : 0 ≤ x)
      have h : Q ≤ ⌊x⌋₊ := by omega
      have : (Q : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h
      rw [Nat.cast_sub hQ]
      push_cast
      linarith
    · rw [Nat.cast_sub hQ]
      push_cast
      linarith

private theorem choose_adjacent {Q : ℕ} (b : ℕ) (hb : b + 1 ≤ Q) :
    (Q.choose (b + 1) : ℝ) / Q.choose b = ((Q : ℝ) - b) / ((b : ℝ) + 1) := by
  have hc : (0 : ℝ) < Q.choose b := by exact_mod_cast Nat.choose_pos (by omega : b ≤ Q)
  apply (div_eq_div_iff hc.ne' (by positivity)).mpr
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq Q b)
  push_cast [Nat.cast_sub (by omega : b ≤ Q)] at h
  linarith only [h]

/-- The logarithmic forms of `H₊/H = Q^(s+o(1))` and `H₋/H = Q^(-s+o(1))`.
The three degrees are `b`, `b+1`, and `b+2`, with the central degree `b+1`.
Both upper bounds are exact, and both lower bounds have additive error two. -/
theorem relocation_level_bounds {Q : ℕ} (hQ : 2 ≤ Q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ, b + 2 ≤ Q ∧
      logb 2 (Q.choose (b + 2)) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (s * logb 2 Q - 2) (s * logb 2 Q) ∧
      logb 2 (Q.choose b) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (-(s * logb 2 Q) - 2) (-(s * logb 2 Q)) := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ₀ : (0 : ℝ) < Q := by linarith
  let r := (Q : ℝ) ^ s
  have hr : 0 < r := Real.rpow_pos_of_pos hQ₀ _
  have hr₁ : (Q : ℝ)⁻¹ ≤ r := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.1
  have hr₂ : r ≤ Q := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.2
  have hQr : 1 ≤ (Q : ℝ) * r := by simpa [mul_comm] using (inv_le_iff_one_le_mul₀ hQ₀).mp hr₁
  have hden : 0 < 1 + r := by linarith
  obtain ⟨b, hb, hbx, hxb⟩ := interior_floor hQ
    ((le_div_iff₀ hden).mpr (by linarith : 1 * (1 + r) ≤ (Q : ℝ) + 1))
    ((div_le_iff₀ hden).mpr (by linarith))
  have hbx' := (le_div_iff₀ hden).mp hbx
  have hxb' := (div_le_iff₀ hden).mp hxb
  let A := (Q : ℝ) - b - 1
  let B := (b : ℝ) + 1
  have hA : 1 ≤ A := by
    have : (b : ℝ) + 2 ≤ Q := by exact_mod_cast hb
    dsimp [A]
    linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) b]
  let p := A / (B + 1)
  let m := B / (A + 1)
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hm : 0 < m := div_pos (by linarith) (by linarith)
  have hPu : p ≤ r := by
    apply (div_le_iff₀ (by linarith : 0 < B + 1)).mpr
    dsimp [A, B]
    linarith only [hxb']
  have hMu : m ≤ r⁻¹ := by
    rw [← one_div, div_le_div_iff₀ (by linarith : 0 < A + 1) hr]
    dsimp [A, B]
    linarith only [hbx']
  have hprod : 1 / 4 ≤ p * m := by
    dsimp [p, m]
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hlprod := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1 / 4) hprod
  have hlog : logb 2 (1 / 4) = -2 := by
    rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [hlog, Real.logb_mul hp.ne' hm.ne'] at hlprod
  have hpl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hPu
  have hml := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hm hMu
  have hlr : logb 2 r = s * logb 2 Q := Real.logb_rpow_eq_mul_logb_of_pos hQ₀
  rw [hlr] at hpl
  rw [Real.logb_inv, hlr] at hml
  have hc (k : ℕ) (hk : k ≤ Q) : (0 : ℝ) < Q.choose k := by exact_mod_cast Nat.choose_pos hk
  have hp' : (Q.choose (b+2) : ℝ) / Q.choose (b+1) = p := by
    convert choose_adjacent (b + 1) hb using 1
    dsimp [p, A, B]
    push_cast
    ring
  have hm' : (Q.choose b : ℝ) / Q.choose (b+1) = m := by
    rw [← inv_div, choose_adjacent b (by omega), inv_div]
    dsimp [m, A, B]
    ring
  refine ⟨b, hb, ?_, ?_⟩
  · rw [← Real.logb_div (hc _ hb).ne' (hc _ (by omega)).ne', hp']
    exact ⟨by linarith, hpl⟩
  · rw [← Real.logb_div (hc _ (by omega)).ne' (hc _ (by omega)).ne', hm']
    exact ⟨by linarith, hml⟩

/-- A dyadic dimension realizes any threshold in the interval of permitted
logarithmic price slopes, including the zero-cost case. -/
theorem relocation_level_bounds_for_threshold {n : ℕ} (hn : 0 < n) {t c : ℝ}
    (ht : 0 ≤ t) (hc : |c| ≤ n * t) :
    ∃ b : ℕ, b + 2 ≤ 2^n ∧
      t * (logb 2 ((2^n : ℕ).choose (b + 2)) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ c ∧
      t * (logb 2 ((2^n : ℕ).choose b) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ -c := by
  have hQ : 2 ≤ (2 : ℕ)^n := Nat.le_pow hn
  have hlog : logb 2 ((2^n : ℕ) : ℝ) = n := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  obtain ⟨s, hs, hcs⟩ : ∃ s ∈ Set.Icc (-1 : ℝ) 1, t * (s * n) = c := by
    rcases ht.eq_or_lt with rfl | ht'
    · have hc' : c = 0 := by simpa using hc
      exact ⟨0, by constructor <;> norm_num, by simp [hc']⟩
    have hnt : 0 < (n : ℝ) * t := by positivity
    refine ⟨c / (n * t), ⟨(le_div_iff₀ hnt).mpr ?_, (div_le_iff₀ hnt).mpr ?_⟩, ?_⟩
    · linarith [(abs_le.mp hc).1]
    · linarith [(abs_le.mp hc).2]
    · field_simp
  obtain ⟨b, hb, hp, hm⟩ := relocation_level_bounds hQ hs
  rw [hlog] at hp hm
  refine ⟨b, hb, (mul_le_mul_of_nonneg_left hp.2 ht).trans_eq hcs, ?_⟩
  exact (mul_le_mul_of_nonneg_left hm.2 ht).trans_eq (by rw [mul_neg, hcs])

open Filter
open scoped Topology

private theorem ratio_slope_limit {f : ℕ → ℝ} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, f n ∈ Set.Icc (n * a - 2) (n * a)) :
    Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 a) := by
  have hl : Tendsto (fun n : ℕ ↦ a - 2 / (n : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    rw [sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith only [h.1]
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    exact (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by linarith only [h.2])

/-- Choosing adjacent degrees at every tensor power realizes the two
opposite slopes in the limit, after division by the power. -/
theorem relocation_level_limits {q : ℕ} (hq : 2 ≤ q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, b n + 2 ≤ q^n) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n + 2)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (-(logb 2 q * s))) := by
  classical
  choose f hf using fun (n : ℕ) (hn : 0 < n) ↦ relocation_level_bounds (hq.trans (Nat.le_pow hn)) hs
  let b (n : ℕ) := if hn : 0 < n then f n hn else 0
  refine ⟨b, ?_, ratio_slope_limit ?_, ratio_slope_limit ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simpa [b, hn] using (hf n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.1
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.2
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h

end SpectralBooks
end LinearAlgebra
end OAI
