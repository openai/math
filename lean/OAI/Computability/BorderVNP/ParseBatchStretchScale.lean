import OAI.Computability.BorderVNP.DiagonalAdvice
import OAI.Computability.BorderVNP.ParseBatchUniversal

/-!
# Instantiating the parse network at the stretch scales of Section 9

The replication exponent of the verified compiler is 24. Its cubic logarithm
costs at most a factor `n^Δ` when the batch exponent is chosen below `Δ/3`.
The estimates use the integer floors in the manuscript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open Filter Diagonal

/-- Every sufficiently large stretched-exponential batch meets the polynomial
replication requirement in Lemma 2.3, even at the full candidate gate size. -/
theorem eventually_replication {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) :
    ∀ᶠ n : ℕ in atTop, (n + stretch σ n + 2)^24 ≤ stretch ρ n := by
  filter_upwards [advice_polynomial_lt_batch hσ hσρ (3^24) 24, eventually_ge_atTop 1] with n h hn
  have hnM : n + stretch σ n ≤ adviceScale σ ρ n := by unfold adviceScale; omega
  have hM : 1 ≤ adviceScale σ ρ n := by omega
  calc
    _ ≤ (3 * adviceScale σ ρ n)^24 := Nat.pow_le_pow_left (by omega) 24
    _ ≤ _ := by rw [mul_pow]; exact h.le

/-- The exact degree-three query network fits the initial `r*n^(1+Δ)` volume
budget at the chosen stretched-exponential batch size. -/
theorem eventually_parse_volume {ρ Δ : ℝ} (hρ : 0 < ρ) (hΔ : 3*ρ < Δ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch ρ n
      (180000000 * (n*r) * (Nat.clog 2 (2*n*r)+3)^3 : ℕ) ≤
        (r : ℝ)*(n : ℝ)^(1+Δ) := by
  have hlog := ((isLittleO_log_rpow_atTop hρ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (Real.log_pos (by norm_num : 1 < (2 : ℝ)))
  filter_upwards [hlog, TeamScales.eventually_rpow_gap hΔ (180000000*343), eventually_ge_atTop 1]
    with n hlog hgap hn
  let r := stretch ρ n
  let x := (n : ℝ)^ρ
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := zero_lt_one.trans_le hn'
  have hx : 1 ≤ x := Real.one_le_rpow hn' hρ.le
  have hnr : 1 ≤ r := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ x from by simpa only [Nat.cast_one] using Real.one_le_rpow (by norm_num : 1 ≤ (2 : ℝ)) (zero_le_one.trans hx))
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hnr
  have hrp := zero_lt_one.trans_le hr'
  have hl : Real.logb 2 n ≤ x := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr
    simpa only [x, Function.comp_apply, Real.norm_of_nonneg (Real.log_nonneg hn'),
      Real.norm_of_nonneg (Real.rpow_nonneg hnp.le ρ), mul_comm] using hlog
  have hrl : Real.logb 2 r ≤ x := (Real.logb_le_iff_le_rpow (by norm_num) hrp).mpr (Nat.floor_le (by positivity))
  have hN : 1 ≤ 2 * (n : ℝ) * r := by nlinarith
  have hlr := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hN)
  have hcast : (2*(n : ℝ)*r) = ((2*n*r : ℕ) : ℝ) := by push_cast; rfl
  have hceil := Real.natCeil_logb_natCast 2 (2*n*r)
  simp only [Nat.cast_ofNat] at hceil
  rw [hcast, hceil, ← hcast, Real.logb_mul (by positivity) hrp.ne',
    Real.logb_mul (by norm_num) hnp.ne', Real.logb_self_eq_one (by norm_num)] at hlr
  have hb : (Nat.clog 2 (2*n*r) : ℝ)+3 ≤ 7*x := by linarith
  have hcube := pow_le_pow_left₀ (by positivity) hb 3
  have hx3 : x^3 = (n : ℝ)^(3*ρ) := by
    rw [← Real.rpow_mul_natCast hnp.le]; congr 1; ring
  have hbudget : 180000000 * ((Nat.clog 2 (2*n*r) : ℝ)+3)^3 ≤ (n : ℝ)^Δ := calc
    _ ≤ 180000000 * (7*x)^3 := mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ = (180000000*343) * (n : ℝ)^(3*ρ) := by rw [← hx3]; ring
    _ ≤ _ := hgap
  change ((180000000*(n*r)*(Nat.clog 2 (2*n*r)+3)^3 : ℕ) : ℝ) ≤ _
  push_cast
  rw [Real.rpow_add hnp, Real.rpow_one]
  calc
    _ = ((r : ℝ)*n) * (180000000 * ((Nat.clog 2 (2*n*r) : ℝ)+3)^3) := by ring
    _ ≤ ((r : ℝ)*n) * (n : ℝ)^Δ := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
