import OAI.LinearAlgebra.FiniteFourier.PackedDescent
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Using the whole array width in a synchronized kernel bound

An array of width at most a constant times the parent length can be charged
using its logarithm even when a synchronized kernel slot has many fewer
active axes. The extra logarithm of the prime-axis cutoff is absorbed by an
arbitrarily small increase of the exponent.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Real Filter

/-- Before normalization, use the logarithm of the parent length as an upper
bound on the exponent of any shear tensor on its working array. -/
noncomputable def PrimeJetPacking.widthWork {P : Finset ℕ} {n e : ℕ} {B : ℝ}
    (pack : PrimeJetPacking P n e B) (C β : ℝ) (cutoff : ℕ) : ℝ :=
  C*n*(1+log B)^2*((1+logb 2 n)^β + (1+log (2+pack.jet))*convolutionEnvelope cutoff)

private theorem eventually_gauge_dominates_width {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β < γ) (hγ : γ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ, 1 ≤ B → B ≤ (log n)^2 →
      (1+log B)^2 * (1+logb 2 n)^β ≤ 27 * convolutionGauge γ (log n) := by
  have hT := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha := (isLittleO_log_rpow_rpow_atTop γ (sub_pos.mpr hβγ)).bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [hT.eventually ha, hT.eventually_ge_atTop 3] with n h hn
  intro B hB hb
  let T := log (n:ℝ)
  let L := log T
  change 3 ≤ T at hn
  have ht : 0 < T := by linarith
  have hl : 1 ≤ L := (le_log_iff_exp_le ht).2 (exp_one_lt_three.le.trans hn)
  have hl' : 0 < L := by linarith
  have hscale : L^γ ≤ T^(γ-β) := by
    change ‖L^γ‖ ≤ 1*‖T^(γ-β)‖ at h
    simpa only [Real.norm_of_nonneg (rpow_nonneg hl'.le γ),
      Real.norm_of_nonneg (rpow_nonneg ht.le (γ-β)), one_mul] using h
  have hs : (1+log B)^2 ≤ (3*L)^2 := by
    have hh := log_le_log (by linarith : 0 < B) hb
    rw [log_pow, Nat.cast_ofNat] at hh
    apply pow_le_pow_left₀ (by linarith [log_nonneg hB]) _ 2
    change log B ≤ 2*L at hh
    linarith
  have hlog₂ : 1+logb 2 n ≤ 3*T := by
    have hpos : 0 < log 2 := log_pos (by norm_num)
    have hle : (1:ℝ) ≤ 2*log 2 := by linarith [log_two_gt_d9]
    have hquot : T / log 2 ≤ 2*T := (div_le_iff₀ hpos).2 (by
      have := mul_le_mul_of_nonneg_left hle ht.le
      linarith only [this])
    change 1 + T / log 2 ≤ 3*T
    linarith
  have hnon : 0 ≤ 1+logb 2 n := by
    have : 0 ≤ T / log 2 := div_nonneg ht.le (log_pos (by norm_num : (1:ℝ) < 2)).le
    change 0 ≤ 1+T/log 2
    linarith
  have hpow : (1+logb 2 n)^β ≤ 3*T^β := calc
    _ ≤ (3*T)^β := rpow_le_rpow hnon hlog₂ hβ
    _ = (3:ℝ)^β*T^β := mul_rpow (by norm_num) ht.le
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (rpow_nonneg ht.le β)
      simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) (hβγ.le.trans hγ)
  change _ ≤ 27 * convolutionGauge γ T
  rw [convolutionGauge, max_eq_right hn]
  calc
    _ ≤ (3*L)^2*(3*T^β) := mul_le_mul hs hpow (rpow_nonneg hnon _) (sq_nonneg _)
    _ = 27 * (T^β * L^γ) * L^(2-γ) := by
      have he : L^γ*L^(2-γ) = L^2 := by rw [← rpow_add hl', add_sub_cancel, rpow_two]
      calc
        _ = 27*T^β*(L^γ*L^(2-γ)) := by rw [he]; ring
        _ = _ := by ring
    _ ≤ 27 * (T^β * T^(γ-β)) * L^(2-γ) := by gcongr
    _ = 27*(T^γ*(log T)^(2-γ)) := by
      rw [← rpow_add ht, add_sub_cancel]
      ring

/-- A bound using the logarithm of the global width suffices in the
convolution recurrence at every strictly larger exponent. -/
theorem eventually_widthWork_le {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β < γ) (hγ : γ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ {e s t : ℕ} {P : Finset ℕ} {B C : ℝ}
      (pack : PrimeJetPacking P n e B), 0 ≤ C → 1 ≤ B → B ≤ (log n)^2 → 0 < s → s ≤ t →
      pack.widthWork C β s ≤ 162*C*n*
        (convolutionGauge γ (log n) + (log (log n))^3*convolutionEnvelope t) := by
  have ht := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gauge_dominates_width hβ hβγ hγ, ht.eventually_ge_atTop 3] with n hwidth hT
  intro e s t P B C pack hC hB hb hs hst
  change 3 ≤ log (n:ℝ) at hT
  have hw := hwidth B hB hb
  have hmain := pack.listWork_le hC (hβ.trans hβγ.le) hγ hB hb hT hs hst
  let G := convolutionGauge γ (log n)
  let Q := (log (log n))^3*convolutionEnvelope t
  have hQ : 0 ≤ Q := by
    have := log_nonneg (show 1 ≤ log (n:ℝ) by linarith)
    have := convolutionEnvelope_one_le (hs.trans_le hst)
    dsimp [Q]
    positivity
  have hadd : 0 ≤ C*n*(1+log B)^2*((pack.axes.card : ℝ)+1)^γ := by positivity
  have hc := mul_le_mul_of_nonneg_left hw (mul_nonneg hC (Nat.cast_nonneg (α := ℝ) n))
  have hq := mul_nonneg (mul_nonneg hC (Nat.cast_nonneg (α := ℝ) n)) hQ
  change C*n*(1+log B)^2*(_ + _) ≤ 135*C*n*(G+Q) at hmain
  change C*n*(1+log B)^2*(_ + _) ≤ 162*C*n*(G+Q)
  change C*n*(_ * _) ≤ C*n*(27*G) at hc
  linarith only [hc, hadd, hmain, hq]

end FiniteFourier
end LinearAlgebra
end OAI
