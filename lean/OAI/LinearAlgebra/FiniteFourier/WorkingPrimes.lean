import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Supply of auxiliary primes for the Fourier working lengths

Even after deleting the radix and the field characteristic, the primes between
`t` and `t²` have product larger than `2^(t+1)` for all sufficiently large `t`.
Chebyshev's elementary estimates suffice for this use of the prime number theorem.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Finset Real

section

/-- The auxiliary primes between `t` and `t²`, excluding the two forbidden orders. -/
def workingPrimes (t a b : ℕ) : Finset ℕ :=
  (((Nat.primesLE (t ^ 2)).filter (t ≤ ·)).erase a).erase b

@[simp] theorem mem_workingPrimes {t a b p : ℕ} :
    p ∈ workingPrimes t a b ↔ p.Prime ∧ t ≤ p ∧ p ≤ t ^ 2 ∧ p ≠ a ∧ p ≠ b := by
  simp only [workingPrimes, mem_erase, mem_filter, Nat.mem_primesLE]
  tauto

private theorem sum_le_sum_erase_add {s : Finset ℕ} {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ p ∈ s, log p ≤ c) :
    ∑ p ∈ s, log p ≤ (∑ p ∈ s.erase n, log p) + c := by
  by_cases hn : n ∈ s
  · rw [← sum_erase_add _ _ hn]
    gcongr
    exact h _ hn
  · simpa [erase_eq_of_notMem hn] using hc

private theorem theta_le_working_sum {t : ℕ} (ht : 1 ≤ t) (a b : ℕ) :
    Chebyshev.theta (t ^ 2 : ℕ) ≤ Chebyshev.theta t +
      (∑ p ∈ workingPrimes t a b, log p) + 2 * log ((t : ℝ) ^ 2) := by
  let s := (Nat.primesLE (t ^ 2)).filter (t ≤ ·)
  have htl : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hc : 0 ≤ log ((t : ℝ) ^ 2) := log_nonneg (one_le_pow₀ htl)
  have hcap (p) (hp : p ∈ s) : log p ≤ log ((t : ℝ) ^ 2) := by
    obtain ⟨hp', _⟩ := mem_filter.mp hp
    apply log_le_log (by exact_mod_cast (Nat.prime_of_mem_primesLE hp').pos)
    exact_mod_cast Nat.le_of_mem_primesLE hp'
  have h₁ := sum_le_sum_erase_add (n := a) hc hcap
  have h₂ := sum_le_sum_erase_add (s := s.erase a) (n := b) hc
    (fun p hp ↦ hcap p (mem_of_mem_erase hp))
  have hsmall : (∑ p ∈ (Nat.primesLE (t ^ 2)).filter (fun p ↦ ¬t ≤ p), log p) ≤
      ∑ p ∈ Nat.primesLE t, log p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp', hlt⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_of_mem_primesLE hp'⟩
    · intro p hp _
      exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  have hsplit := sum_filter_add_sum_filter_not (Nat.primesLE (t ^ 2)) (t ≤ ·) (fun p ↦ log p)
  change (∑ p ∈ s, log p) + _ = _ at hsplit
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  change _ ≤ _ + (∑ p ∈ (s.erase a).erase b, log p) + _
  linarith

/-- Uniformly in the two exclusions, Chebyshev's lower bound supplies the
required product of auxiliary primes. -/
theorem eventually_pow_lt_prod_workingPrimes :
    ∀ᶠ t : ℕ in atTop, ∀ a b : ℕ, 2 ^ (t + 1) < ∏ p ∈ workingPrimes t a b, p := by
  have hslow := (isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hslow, eventually_ge_atTop 128]
    with t hlog ht a b
  have htr : (128 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have htl := log_nonneg (show (1 : ℝ) ≤ t by linarith)
  simp only [Real.norm_eq_abs, id, abs_of_nonneg htl, abs_of_pos htpos] at hlog
  have hlog2lo : (1 : ℝ) / 2 < log 2 := by linarith [log_two_gt_d9]
  have hlog2hi : log 2 ≤ 1 := by linarith [log_two_lt_d9]
  have hlo := Chebyshev.theta_ge (t ^ 2)
  push_cast at hlo
  rw [sqrt_sq htpos.le, log_pow] at hlo
  have hu := Chebyshev.theta_le_log4_mul_x htpos.le
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow] at hu
  have hmass := theta_le_working_sum (show 1 ≤ t by omega) a b
  push_cast at hmass
  rw [log_pow] at hmass
  norm_num1 at hlo hu hmass
  have hlogadd : log ((t : ℝ) ^ 2 + 1) ≤ 2 * t := by
    calc
      _ ≤ log (((t : ℝ) + 1) ^ 2) := log_le_log (by positivity) (by nlinarith)
      _ ≤ 2 * t := by
        rw [log_pow]
        norm_num1
        linarith [log_le_sub_one_of_pos (show 0 < (t : ℝ) + 1 by positivity)]
  have hsum : ((t : ℝ) + 1) * log 2 < ∑ p ∈ workingPrimes t a b, log p := by
    nlinarith only [hlo, hu, hmass, hlogadd, mul_le_mul_of_nonneg_left hlog htpos.le,
      mul_le_mul_of_nonneg_left hlog2lo.le (sq_nonneg (t : ℝ)),
      mul_le_mul_of_nonneg_left hlog2hi htpos.le, hlog2hi, hlog,
      mul_nonneg (sub_nonneg.mpr htr) htpos.le, htr]
  have hp (p) (hp : p ∈ workingPrimes t a b) : (0 : ℝ) < p := by
    exact_mod_cast (mem_workingPrimes.mp hp).1.pos
  have hcmp : ((2 : ℝ) ^ (t + 1)) < ∏ p ∈ workingPrimes t a b, (p : ℝ) := by
    apply (log_lt_log_iff (by positivity) (prod_pos hp)).mp
    rw [log_prod (fun p hp' ↦ (hp p hp').ne'), log_pow]
    push_cast
    exact hsum
  rw [← Nat.cast_prod] at hcmp
  exact_mod_cast hcmp

/-- The remaining primes in the paper's construction have product greater than
`2N` for every `N ≤ 2^t`, with a single threshold in `t`. -/
theorem eventually_two_mul_lt_prod_workingPrimes :
    ∀ᶠ t : ℕ in atTop, ∀ a b N : ℕ, N ≤ 2 ^ t →
      2 * N < ∏ p ∈ workingPrimes t a b, p := by
  filter_upwards [eventually_pow_lt_prod_workingPrimes] with t ht a b N hN
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hN) (by simpa [pow_succ, Nat.mul_comm] using ht a b)

end

end FiniteFourier
end LinearAlgebra
end OAI
