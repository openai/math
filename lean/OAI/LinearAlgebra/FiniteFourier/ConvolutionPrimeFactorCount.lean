import OAI.LinearAlgebra.FiniteFourier.ConvolutionAxisCount
import Mathlib.Data.Nat.Factorization.Basic

/-! # The number of odd-prime color constraints -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Real

/-- The number of ordered pairs of subsets of the prime factors of any integer
up to `B²` grows more slowly than every positive power of `B`. -/
theorem eventually_two_pow_twice_card_primeFactors_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ n ≤ B ^ 2,
      (2 : ℝ) ^ (2 * n.primeFactors.card) ≤ (B : ℝ) ^ ε := by
  have hloglog : Tendsto (fun B : ℕ => log (log (B : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually_ge_atTop (36 * log 2 / ε),
    eventually_ge_atTop (3 : ℕ)] with B hthreshold hB
  have hB₁ : 1 < (B : ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hBpos : 0 < (B : ℝ) := lt_trans zero_lt_one hB₁
  have hlog := log_pos hB₁
  have hlogSq : log ((B ^ 2 : ℕ) : ℝ) = 2 * log B := by
    rw [Nat.cast_pow, log_pow, Nat.cast_ofNat]
  have hscale : 36 * log 2 ≤ log (log ((B ^ 2 : ℕ) : ℝ)) * ε := by
    apply (div_le_iff₀ hε).mp
    refine hthreshold.trans (log_le_log hlog ?_)
    rw [hlogSq]
    linarith
  intro n hn
  rcases n.eq_zero_or_pos with rfl | hpos
  · simpa using one_le_rpow hB₁.le hε.le
  have hfac := factorial_card_le_prod n.primeFactors (fun _ => Nat.pos_of_mem_primeFactors)
  have hcard := axisCount_le_log_div_loglog (n := B ^ 2) (by nlinarith)
    (hfac.trans ((Nat.le_of_dvd hpos n.prod_primeFactors_dvd).trans hn))
  have hden : 0 < log (log ((B ^ 2 : ℕ) : ℝ)) := by
    have hleft := mul_pos (by norm_num : 0 < (36 : ℝ)) (log_pos (by norm_num : 1 < (2 : ℝ)))
    exact pos_of_mul_pos_left (hleft.trans_le hscale) hε.le
  have hcard' := (le_div_iff₀ hden).mp hcard
  rw [hlogSq] at hcard' hscale
  apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hBpos ε)).mp
  rw [log_pow, log_rpow hBpos]
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right hcard' hε.le,
    mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg n.primeFactors.card : (0 : ℝ) ≤ _)]

end FiniteFourier
end LinearAlgebra
end OAI
