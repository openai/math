import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimes
import OAI.LinearAlgebra.FiniteFourier.ConvolutionRecurrence

/-! # Work per coefficient at the packed parameters

Both cutoffs in the convolution descent are eventually bounded by `T²`,
where `T = log n`. The axis count saves one power of `log T` in the tensor
term. The divide-and-conquer Taylor shifts use one further logarithm in the
term for shorter products.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Real

/-- A common cutoff estimate for the linear and the power-law choices of `B`.
It applies with coefficients `3/c₀` and `1` and powers `1` and `1+η/3`. -/
theorem eventually_ceil_power_le_sq {c a : ℝ} (hc : 0 ≤ c) (ha₀ : 0 ≤ a) (ha : a < 2) :
    ∀ᶠ T : ℝ in Filter.atTop, (⌈c * T^a⌉₊ : ℝ) ≤ T^2 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr ha)).eventually_ge_atTop (c+1)] with T hT hscale
  have hpower := one_le_rpow hT ha₀
  have hpos : 0 < T := zero_lt_one.trans_le hT
  calc
    _ ≤ c * T^a + 1 := (Nat.ceil_lt_add_one (mul_nonneg hc (rpow_nonneg hpos.le a))).le
    _ ≤ (c+1)*T^a := by linarith
    _ ≤ T^(2-a)*T^a := mul_le_mul_of_nonneg_right hscale (rpow_nonneg hpos.le a)
    _ = T^2 := by rw [← rpow_add hpos, sub_add_cancel, rpow_two]

/-- Normalized cost at any of the prime and jet packings, with an explicit
common constant for both contributions. -/
theorem PrimeJetPacking.normalizedCost_le {P : Finset ℕ} {n e : ℕ} {B β μ : ℝ}
    (s : PrimeJetPacking P n e B) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hμ : 0 ≤ μ) (hB : 1 ≤ B) (hcut : B ≤ (log n)^2) (hT : 3 ≤ log n) :
    (1+log B)^2 * (((s.axes.card : ℝ)+1)^β + (1+log (2+s.jet))*μ) ≤
      135 * (convolutionGauge β (log n) + (log (log n))^3 * μ) := by
  let T := log n
  let L := log T
  have ht : 3 ≤ T := hT
  have htpos : 0 < T := by linarith
  have hL : 1 ≤ L := ((lt_log_iff_exp_lt htpos).mpr (exp_one_lt_three.trans_le ht)).le
  have hl : 0 < L := by linarith
  have hlogB : log B ≤ 2*L := by
    have hh := log_le_log (show 0 < B by linarith) hcut
    simpa [T, L, log_pow] using hh
  have hb : 0 ≤ 1+log B := by linarith [log_nonneg hB]
  have hsquare : (1+log B)^2 ≤ (3*L)^2 := pow_le_pow_left₀ hb (by linarith) _
  have hcount : (s.axes.card : ℝ) + 1 ≤ 10*T/L := by
    have hc := (le_div_iff₀ hl).mp s.count_le
    apply (le_div_iff₀ hl).mpr
    nlinarith only [hc, log_le_self htpos.le]
  have hten : (10 : ℝ)^β ≤ 10 := by
    simpa using rpow_le_rpow_of_exponent_le (show 1 ≤ (10 : ℝ) by norm_num) hβ'
  have hsum : (1+log B)^2 * ((s.axes.card : ℝ) + 1)^β ≤ 90 * convolutionGauge β T := calc
    _ ≤ (3*L)^2 * (10*T/L)^β := mul_le_mul hsquare
      (rpow_le_rpow (by positivity) hcount hβ) (by positivity) (sq_nonneg _)
    _ ≤ 90 * (T^β * L^(2-β)) := by
      rw [div_rpow (by positivity) hl.le, mul_rpow (by norm_num : (0:ℝ) ≤ 10) htpos.le,
        rpow_sub hl, rpow_two]
      have hm := mul_le_mul_of_nonneg_right hten (rpow_nonneg htpos.le β)
      have hq := div_le_div_of_nonneg_right hm (rpow_nonneg hl.le β)
      calc
        _ ≤ (3*L)^2 * ((10*T^β)/L^β) := mul_le_mul_of_nonneg_left hq (sq_nonneg _)
        _ = _ := by ring
    _ = _ := by simp [convolutionGauge, max_eq_right ht, L]
  have hentry : 2+(s.jet : ℝ) ≤ 11 * B^2 := by
    nlinarith only [s.jet_upper, one_le_pow₀ hB (n := 2)]
  have hjet : 1+log (2+(s.jet : ℝ)) ≤ 15*L := by
    have hj := log_le_log (by positivity : 0 < 2+(s.jet : ℝ)) hentry
    rw [log_mul (by norm_num) (by positivity), log_pow, Nat.cast_ofNat] at hj
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 11)]
  have hj0 : 0 ≤ 1+log (2+(s.jet : ℝ)) := by
    linarith [log_nonneg (show 1 ≤ 2+(s.jet : ℝ) by linarith only [show (0:ℝ) ≤ s.jet by positivity])]
  have hshort := mul_le_mul_of_nonneg_right (mul_le_mul hsquare hjet hj0 (sq_nonneg (3*L))) hμ
  have hg : 0 ≤ convolutionGauge β T := (show (0:ℝ) ≤ 1 by norm_num).trans
    (convolutionGauge_one_le hβ hβ' T)
  change _ ≤ 135 * (convolutionGauge β T + L^3*μ)
  nlinarith only [hsum, hshort, hg]

end FiniteFourier
end LinearAlgebra
end OAI
