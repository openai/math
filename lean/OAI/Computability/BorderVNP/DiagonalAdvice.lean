import OAI.Computability.BorderVNP.TeamScales

/-!
# The parameter and advice scales at the border

Section 9 takes a batch size `r = ⌊2^(n^ρ)⌋`, a hypothesized circuit size
`m₀ = ⌊2^(n^σ)⌋`, and `M = m₀ + n + ⌈log₂(r+1)⌉`. The residue advice,
the matrix pin and the path algorithm occupy only a polynomial in `M`.
The estimates below use the exact integer roundings from the manuscript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter

/-- Stretched-exponential integer bound used for both the candidate size
and the much larger number of processors. -/
noncomputable def stretch (a : ℝ) (n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((n : ℝ) ^ a)⌋₊

/-- Size parameter for the chart, finite field and residue algorithm. -/
noncomputable def adviceScale (σ ρ : ℝ) (n : ℕ) : ℕ :=
  stretch σ n + n + Nat.clog 2 (stretch ρ n + 1)

private theorem eventually_rpow_le_stretch {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, 2 * (n : ℝ) ^ a ≤ (2 : ℝ) ^ ((n : ℝ) ^ σ) := by
  have hs := (tendsto_rpow_atTop hσ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ho := ((isLittleO_rpow_exp_pos_mul_atTop (a / σ)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).comp_tendsto hs).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [ho] with n hn
  change ‖((n : ℝ) ^ σ) ^ (a / σ)‖ ≤ 1 / 2 * ‖Real.exp (Real.log 2 * (n : ℝ) ^ σ)‖ at hn
  rw [← Real.rpow_mul (Nat.cast_nonneg _), show σ * (a / σ) = a by field_simp,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    at hn
  linarith

private theorem clog_stretch_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) :
    ∀ᶠ n : ℕ in atTop, Nat.clog 2 (stretch ρ n + 1) ≤ stretch σ n := by
  filter_upwards [eventually_rpow_le_stretch hσ ρ, eventually_ge_atTop 1] with n hn hnpos
  have hone := Real.one_le_rpow (show 1 ≤ (n : ℝ) by exact_mod_cast hnpos) hρ
  have hf := Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) ^ σ))
  change _ < (stretch σ n : ℝ) + 1 at hf
  have hexp : (n : ℝ) ^ ρ ≤ (stretch σ n : ℝ) := by
    linarith
  have hlt : (n : ℝ) ^ ρ < (stretch σ n : ℝ) := by
    by_cases heq : (n : ℝ) ^ ρ = 1
    · have h : 2 ≤ (2 : ℝ) ^ ((n : ℝ) ^ σ) := by linarith
      have hh : 2 ≤ stretch σ n := Nat.le_floor h
      rw [heq]
      exact_mod_cast (by omega : 1 < stretch σ n)
    · linarith
  have hb := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt
  rw [Real.rpow_natCast] at hb
  have hlo := Nat.floor_le (by positivity : 0 ≤ (2 : ℝ) ^ ((n : ℝ) ^ ρ))
  change (stretch ρ n : ℝ) ≤ _ at hlo
  have hlt' : stretch ρ n < 2 ^ stretch σ n := by exact_mod_cast hlo.trans_lt hb
  exact Nat.clog_le_of_le_pow hlt'

/-- A single threshold in `n` suffices for all sufficiently small quantities
with a *fixed* polynomial bound in `M`, including their constant factors.
The coefficients and exponents of the polynomial may depend on the chosen
shortening, field characteristic, and fixed algorithm. -/
theorem advice_polynomial_lt_batch {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) (A d : ℕ) :
    ∀ᶠ n : ℕ in atTop, A * adviceScale σ ρ n ^ d < stretch ρ n := by
  have hgap := (tendsto_rpow_atTop (sub_pos.mpr hσρ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  let K : ℕ := A * 3 ^ d + 2
  filter_upwards [clog_stretch_le hσ (hσ.trans hσρ).le, eventually_rpow_le_stretch hσ 1,
    hgap.eventually_ge_atTop (d + (K : ℝ) + 1), eventually_ge_atTop 1] with n hlog hn hgap hnpos
  rw [Real.rpow_one] at hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hpos := zero_lt_one.trans_le hn'
  let x : ℝ := (n : ℝ) ^ σ
  have hx : 1 ≤ x := Real.one_le_rpow hn' hσ.le
  have hm : (adviceScale σ ρ n : ℝ) ≤ 3 * 2 ^ x := by
    have hb := Nat.floor_le (by positivity : 0 ≤ (2 : ℝ) ^ ((n : ℝ) ^ σ))
    have hb' : (stretch σ n : ℝ) ≤ 2 ^ x := hb
    have hl' : (Nat.clog 2 (stretch ρ n + 1) : ℝ) ≤ stretch σ n := by exact_mod_cast hlog
    simp only [adviceScale, Nat.cast_add]
    change 2 * (n : ℝ) ≤ 2 ^ x at hn
    linarith
  have hKnat : K ≤ 2 ^ K := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hK : (K : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hKnat
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hdom : x * d + K ≤ (n : ℝ) ^ ρ := by
    have hg := mul_le_mul_of_nonneg_right hgap hxpos.le
    change (_ : ℝ) * x ≤ (n : ℝ) ^ (ρ - σ) * (n : ℝ)^σ at hg
    rw [← Real.rpow_add hpos, sub_add_cancel] at hg
    have hKx := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg K)
    nlinarith
  have hbig : (A : ℝ) * (adviceScale σ ρ n : ℝ) ^ d + 1 < (2 : ℝ) ^ ((n : ℝ) ^ ρ) := by
    let y : ℝ := 2 ^ (x * d)
    have hy : 1 ≤ y := Real.one_le_rpow (by norm_num) (by positivity)
    have hpd := pow_le_pow_left₀ (Nat.cast_nonneg _) hm d
    rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ)^x) d, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hpd
    have hp := mul_le_mul_of_nonneg_left hpd (Nat.cast_nonneg A)
    calc
      _ < (K : ℝ) * y := by
        change (A : ℝ) * _ ≤ (A : ℝ) * (3 ^ d * y) at hp
        simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        nlinarith
      _ ≤ (2 : ℝ) ^ (K : ℝ) * y := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (2 : ℝ) ^ (x * d + K) := by rw [Real.rpow_add (by norm_num)]; dsimp [y]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdom
  exact Nat.succ_le_iff.mp (Nat.le_floor (by push_cast; linarith : ((A * adviceScale σ ρ n ^ d + 1 : ℕ) : ℝ) ≤ _))

end Diagonal

end BorderVNP
end Computability
end OAI
