import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # The thin rectangle in the Fourier circuit lower bound

The definitions follow the parameters in the proposition on the value of a
small computation. Logarithms are base two and the block length is integral.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

/-- Thin side parameter `sqrt (3u/m)`. -/
def thinS (m u : ℝ) : ℝ := Real.sqrt (3 * u / m)
/-- Complementary side parameter. -/
def thinC (m u : ℝ) : ℝ := Real.sqrt (1 - thinS m u ^ 2)
/-- Rectangle normalization. -/
def thinDelta (m u : ℝ) : ℝ := 2 * (thinC m u + thinS m u)
/-- Block length in state compression. -/
def thinBlock (m u : ℝ) : ℕ := ⌊1 / (2 * thinS m u)⌋₊
/-- Rank fraction allowed for the correction. -/
def thinRankFraction (u : ℝ) : ℝ := 2 ^ (-9 * u)
/-- Fourier value at the thin rectangle. -/
def thinFourierValue (m u : ℝ) : ℝ := 2 ^ ((2 + 2 * thinS m u) * m / thinDelta m u)
/-- Target value in each slot of the coefficient estimate. -/
def thinJ (m u : ℝ) : ℝ := (2 : ℝ) ^ (-u) * thinFourierValue m u
/-- Weight per step of a backwards walk. -/
def thinWeight (m u : ℝ) : ℝ := 2 ^ (-2 * thinS m u / thinDelta m u)

/-- Bounds on the side lengths used for rank, support and weight removal. -/
structure ThinBounds (m u : ℝ) : Prop where
  m_pos : 0 < m
  s_pos : 0 < thinS m u
  s_le : thinS m u ≤ 1 / 4
  s_sq_mul : thinS m u ^ 2 * m = 3 * u
  sides_unit : thinC m u ^ 2 + thinS m u ^ 2 = 1
  c_half : 1 / 2 ≤ thinC m u
  c_le : thinC m u ≤ 1
  delta_ge : 2 ≤ thinDelta m u
  delta_le : thinDelta m u ≤ 3
  support_gap : 3 * u ≤ (2 - 2 * thinC m u) * m
  rank_gap : (2 * Real.sqrt ((thinC m u - 1 / 2) ^ 2 + thinS m u ^ 2) - 1) * m ≤ 6 * u

/-- The estimates of the small-computation proposition hold for all `1 ≤ u` and `48u ≤ m`. -/
theorem thinBounds {m u : ℝ} (hu : 1 ≤ u) (hm : 48 * u ≤ m) : ThinBounds m u := by
  have hU : 0 < u := by linarith
  have hM : 0 < m := by linarith
  have hs : 0 < thinS m u := Real.sqrt_pos.2 (by positivity)
  have hs2 : thinS m u ^ 2 = 3 * u / m := Real.sq_sqrt (by positivity)
  have hs2m : thinS m u ^ 2 * m = 3 * u := (eq_div_iff hM.ne').mp hs2
  have hss : thinS m u ^ 2 ≤ 1 / 16 := by rw [hs2]; exact (div_le_iff₀ hM).2 (by linarith)
  have hs4 : thinS m u ≤ 1 / 4 := by nlinarith
  have hc2 : thinC m u ^ 2 = 1 - thinS m u ^ 2 := Real.sq_sqrt (by linarith)
  have hc0 : 0 ≤ thinC m u := Real.sqrt_nonneg _
  have hc5 : 1 / 2 ≤ thinC m u := by nlinarith
  have hc1 : thinC m u ≤ 1 := by nlinarith [sq_nonneg (thinS m u)]
  have hcS : 1 ≤ thinC m u + thinS m u := by
    nlinarith [mul_nonneg hc0 hs.le, sq_nonneg (1 - thinC m u - thinS m u)]
  have hgap : thinS m u ^ 2 ≤ 2 - 2 * thinC m u := by nlinarith [sq_nonneg (1 - thinC m u)]
  have hrad : 2 * Real.sqrt ((thinC m u - 1 / 2) ^ 2 + thinS m u ^ 2) ≤ 1 + 2 * thinS m u ^ 2 := by
    have hroot := Real.sq_sqrt (add_nonneg (sq_nonneg (thinC m u - 1 / 2)) (sq_nonneg (thinS m u)))
    have low : 1 - thinC m u ≤ thinS m u ^ 2 := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    nlinarith [sq_nonneg (thinS m u ^ 2), sq_nonneg (thinS m u)]
  refine ⟨hM, hs, hs4, hs2m, by linarith, hc5, hc1, ?_, ?_, ?_, ?_⟩
  · dsimp [thinDelta]; linarith
  · dsimp [thinDelta]; linarith
  · rw [← hs2m]; exact mul_le_mul_of_nonneg_right hgap hM.le
  · linarith only [mul_le_mul_of_nonneg_right (show 2 * Real.sqrt ((thinC m u - 1 / 2) ^ 2 +
        thinS m u ^ 2) - 1 ≤ 2 * thinS m u ^ 2 by linarith) hM.le, hs2m]

theorem thinFourierValue_pos (m u : ℝ) : 0 < thinFourierValue m u := Real.rpow_pos_of_pos (by norm_num) _

theorem thinJ_pos (m u : ℝ) : 0 < thinJ m u := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (thinFourierValue_pos m u)

private theorem thinJ_rpow (m u : ℝ) :
    thinJ m u = (2 : ℝ) ^ (-u + (2 + 2 * thinS m u) * m / thinDelta m u) := by
  simp only [thinJ, thinFourierValue, Real.rpow_add (by norm_num : (0:ℝ) < 2)]

theorem thinWeight_pos (m u : ℝ) : 0 < thinWeight m u := Real.rpow_pos_of_pos (by norm_num) _

theorem thinWeight_le_one {m u : ℝ} (h : ThinBounds m u) : thinWeight m u ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (div_nonpos_of_nonpos_of_nonneg
    (by linarith only [h.s_pos]) (by linarith only [h.delta_ge]))

theorem thinBlock_pos {m u : ℝ} (h : ThinBounds m u) : 0 < thinBlock m u := by
  apply Nat.floor_pos.2 ((le_div_iff₀ (by linarith only [h.s_pos])).2 ?_)
  linarith only [h.s_le]

/-- Per-output support `2^i` at `j` slots gives a weighted value at most `J^j`.
The hypothesis is the support estimate in log form, using `m = log₂ N`. -/
theorem weighted_walk_le {m u ν : ℝ} (hu : 1 ≤ u) (h : ThinBounds m u) {j i : ℕ}
    (hν : 0 < ν) (hsupport : thinDelta m u * Real.logb 2 ν ≤
      thinDelta m u * ((j : ℝ) * m) + 2 * thinS m u * i) :
    thinWeight m u ^ i * ν ≤ thinJ m u ^ j := by
  have hd : 0 < thinDelta m u := by linarith only [h.delta_ge]
  have hJ : m ≤ -u + (2 + 2 * thinS m u) * m / thinDelta m u := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hd]
    have hud := mul_le_mul_of_nonneg_left h.delta_le (by linarith : 0 ≤ u)
    dsimp only [thinDelta] at hud ⊢
    linarith only [hud, h.support_gap]
  have hν' : Real.logb 2 ν ≤ j * m + 2 * thinS m u * i / thinDelta m u := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hd]
    linarith only [hsupport]
  rw [thinWeight, thinJ_rpow, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hν,
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    _ ≤ (j : ℝ) * m := by
      ring_nf at hν' ⊢
      linarith only [hν']
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg j)

/-- The `t=1/2` rank estimate at rank at most `2^(-9u) N` gives `ν ≤ J`. -/
theorem small_rank_le {m u ν R : ℝ} (hu : 1 ≤ u) (h : ThinBounds m u) (hν : 0 < ν)
    (hR : 0 < R) (hrank : R ≤ thinRankFraction u * (2 : ℝ) ^ m)
    (hprice : thinDelta m u * Real.logb 2 ν ≤
      2 * m * (thinS m u + Real.sqrt ((thinC m u - 1 / 2)^2 + thinS m u ^ 2)) + Real.logb 2 R) :
    ν ≤ thinJ m u := by
  have hd : 0 < thinDelta m u := by linarith only [h.delta_ge]
  have hlog : Real.logb 2 R ≤ -9 * u + m := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hR).2
    simpa [thinRankFraction, Real.rpow_add (by norm_num : (0:ℝ) < 2)] using hrank
  rw [thinJ_rpow, ← Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hν, ← sub_le_iff_le_add',
    le_div_iff₀ hd]
  have hud := mul_le_mul_of_nonneg_left h.delta_le (by linarith : 0 ≤ u)
  linarith only [hprice, hlog, hud, h.rank_gap]

/-- Removing at most `2b` weights costs a factor of two. -/
theorem remove_weight_le_two {m u : ℝ} (h : ThinBounds m u) {d : ℕ} (hd : d ≤ 2 * thinBlock m u) :
    thinWeight m u ^ (-(d : ℝ)) ≤ 2 := by
  have hδ : 0 < thinDelta m u := by linarith only [h.delta_ge]
  have hsb : 0 < 2 * thinS m u := by linarith only [h.s_pos]
  have hb : (thinBlock m u : ℝ) ≤ 1 / (2 * thinS m u) := Nat.floor_le (by positivity)
  have hb' := (le_div_iff₀ hsb).mp hb
  have hd' : (d : ℝ) ≤ 2 * (thinBlock m u : ℝ) := by exact_mod_cast hd
  rw [thinWeight, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  calc
    (2 : ℝ) ^ (-2 * thinS m u / thinDelta m u * -(d : ℝ)) ≤ 2 ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
      linarith only [mul_le_mul_of_nonneg_left hd' hsb.le, hb', h.delta_ge]
    _ = _ := Real.rpow_one _

/-- Substituting the rank and walk bounds into the weighted coefficient estimate. -/
theorem small_computation_value_le {m u ν : ℝ} (h : ThinBounds m u) {d : ℕ}
    (hd : d ≤ 2 * thinBlock m u)
    (htransfer : ν ≤ thinJ m u + thinWeight m u ^ (-(d : ℝ)) * (thinJ m u + thinJ m u)) :
    ν ≤ 5 * (2 : ℝ) ^ (-u) * thinFourierValue m u := by
  have hJ := (thinJ_pos m u).le
  have hwt := mul_le_mul_of_nonneg_right (remove_weight_le_two h hd) (add_nonneg hJ hJ)
  dsimp [thinJ] at hwt htransfer
  linarith only [hwt, htransfer]

/-- The block length at the saturating choice `u=3`. -/
theorem thinBlock_three {m : ℝ} (hm : 0 < m) : thinBlock m 3 = ⌊Real.sqrt m / 6⌋₊ := by
  unfold thinBlock thinS
  rw [Real.sqrt_div (by norm_num)]
  norm_num
  congr 1
  field_simp [(Real.sqrt_pos_of_pos hm).ne']
  ring

/-- If saturation excludes the small-rank budget at `u=3`, then the number of
states exceeds the explicit bound in the quantitative Fourier theorem. -/
theorem fourier_lower_quantitative {N S : ℕ} {m : ℝ} (hm : 144 ≤ m)
    (hsmall : 2 * (S : ℝ) / thinBlock m 3 ≤ thinRankFraction 3 * N →
      thinFourierValue m 3 ≤ 5 * (2 : ℝ) ^ (-(3 : ℝ)) * thinFourierValue m 3) :
    (2 : ℝ) ^ (-(28 : ℝ)) * N * ⌊Real.sqrt m / 6⌋₊ < S := by
  have h := thinBounds (u := 3) (by norm_num) (by linarith : 48 * 3 ≤ m)
  have hF : 0 < thinFourierValue m 3 := Real.rpow_pos_of_pos (by norm_num) _
  have hbad : ¬ 2 * (S : ℝ) / thinBlock m 3 ≤ thinRankFraction 3 * N := by
    intro hbudget
    have hh := hsmall hbudget
    norm_num [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)] at hh
    linarith only [hh, hF]
  have hpos : 0 < (thinBlock m 3 : ℝ) := by exact_mod_cast thinBlock_pos h
  have hlarge := (lt_div_iff₀ hpos).mp (lt_of_not_ge hbad)
  rw [thinBlock_three h.m_pos] at hlarge
  norm_num [thinRankFraction, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)] at hlarge ⊢
  linarith only [hlarge]

/-- The floor in the explicit quantitative bound costs at most a factor of two
for `m ≥ 144`. -/
theorem fourier_sqrt_lower_of_quantitative {N S : ℕ} {m : ℝ} (hm : 144 ≤ m)
    (hS : (2 : ℝ) ^ (-(28 : ℝ)) * N * ⌊Real.sqrt m / 6⌋₊ < S) :
    1 / (12 * 2 ^ 28 : ℝ) * N * Real.sqrt m < S := by
  have hs : (12 : ℝ) ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hfloor := Nat.sub_one_lt_floor (Real.sqrt m / 6)
  have hf : Real.sqrt m / 12 ≤ (⌊Real.sqrt m / 6⌋₊ : ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_left hf (show 0 ≤ (2 : ℝ) ^ (-(28 : ℝ)) * N by positivity)
  norm_num [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)] at hh hS ⊢
  linarith only [hS, hh]

/-- Use one necessary state for the bounded orders to obtain an absolute
positive implied constant valid at every order `N ≥ 2`. -/
theorem uniform_fourier_sqrt_lower : ∃ κ : ℝ, 0 < κ ∧ ∀ N S : ℕ, 2 ≤ N → 0 < S →
    (144 ≤ Real.logb 2 N → (2 : ℝ) ^ (-(28 : ℝ)) * N * ⌊Real.sqrt (Real.logb 2 N) / 6⌋₊ < S) →
    κ * N * Real.sqrt (Real.logb 2 N) ≤ S := by
  refine ⟨1 / (12 * 2 ^ 144), by positivity, ?_⟩
  intro N S hN hS hlarge
  by_cases hm : 144 ≤ Real.logb 2 N
  · apply le_trans _ (fourier_sqrt_lower_of_quantitative hm (hlarge hm)).le
    gcongr <;> norm_num
  · have hn' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have horder : (N : ℝ) ≤ 2 ^ (144 : ℕ) := by
      have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hn').mp (le_of_not_ge hm)
      simpa using hh
    have hsqrt : Real.sqrt (Real.logb 2 N) ≤ 12 :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
    have hh := mul_le_mul horder hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hS' : (1:ℝ) ≤ S := by exact_mod_cast hS
    calc
      _ ≤ 1 / (12 * 2 ^ 144 : ℝ) * ((2 : ℝ) ^ (144 : ℕ) * 12) := by
        rw [mul_assoc]; gcongr
      _ = 1 := by norm_num
      _ ≤ _ := hS'

end

end

end FiniteFourier
end LinearAlgebra
end OAI
