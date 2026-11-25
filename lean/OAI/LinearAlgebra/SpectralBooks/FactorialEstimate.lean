import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Size of a balanced word class

For words on `R` letters with each letter occurring `k` times, the multinomial
identity controls the loss from `R * k * log₂ R` by an explicit logarithmic
error. This gives the word-count estimate in the permutation stretch lemma.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real Filter
open scoped Topology

private theorem log_factorial_upper {n : ℕ} (hn : 0 < n) :
    log n.factorial ≤ n * log n - n + 1 + log n / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le j)
  change log (Stirling.stirlingSeq (j+1)) ≤ log (Stirling.stirlingSeq 1) at h
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
      log_div (exp_pos 1).ne' (by positivity), log_exp, log_sqrt (by norm_num)] at h
  rw [log_div (by positivity) (exp_pos 1).ne', log_exp, log_mul (by norm_num) (by positivity)] at h
  linarith

/-- A balanced multinomial coefficient has at most a logarithmic loss in its
base-two logarithm compared with the number of all words. -/
theorem balanced_logb_lower {R k N : ℕ} (hR : 0 < R) (hk : 0 < k)
    (hN : N * k.factorial ^ R = (R * k).factorial) :
    (R : ℝ) * k * logb 2 R - R * (1 / log 2 + logb 2 k / 2) ≤ logb 2 N := by
  have hNpos : 0 < N := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hN
    exact Nat.factorial_ne_zero _ hN.symm
  have hreal : (N : ℝ) * (k.factorial : ℝ) ^ R = ((R*k).factorial : ℝ) := by
    exact_mod_cast hN
  have hlog := congrArg log hreal
  rw [log_mul (by positivity) (by positivity), log_pow] at hlog
  have lo := Stirling.le_log_factorial_stirling (Nat.mul_pos hR hk).ne'
  have hmk : 0 ≤ log ((R*k : ℕ) : ℝ) := log_nonneg (by exact_mod_cast Nat.mul_pos hR hk)
  have hpi : 0 ≤ log (2 * π) := log_nonneg (by linarith [Real.two_le_pi])
  have a : ((R*k : ℕ) : ℝ) * log ((R*k : ℕ) : ℝ) - ((R*k : ℕ) : ℝ) ≤
      log (N : ℝ) + (R : ℝ) * log (k.factorial : ℝ) := by linarith
  have b := mul_le_mul_of_nonneg_left (log_factorial_upper hk) (Nat.cast_nonneg (α := ℝ) R)
  push_cast at a
  rw [log_mul (by positivity) (by positivity)] at a
  have hass : (R : ℝ) * k * log R - R * (1 + log k / 2) ≤ log N := by linarith
  simpa only [logb, sub_div, mul_div_assoc, add_div, div_right_comm (log k) 2 (log 2)]
    using div_le_div_of_nonneg_right hass (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

/-- The exponential growth rate of the number of balanced words, normalized
by word length along multiples of the alphabet size. -/
theorem tendsto_balanced_logb_div_length {R : ℕ} (hR : 0 < R) (N : ℕ → ℕ)
    (hfactorial : ∀ k, 0 < k → N k * k.factorial ^ R = (R * k).factorial)
    (hcard : ∀ k, 0 < k → N k ≤ R ^ (R * k)) :
    Tendsto (fun k : ℕ ↦ logb 2 (N k) / ((R : ℝ) * k)) atTop (𝓝 (logb 2 R)) := by
  have hlog : Tendsto (fun k : ℕ ↦ logb 2 k / k) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have herr : Tendsto (fun k : ℕ ↦ (1 / log 2) / k + (logb 2 k / k) / 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 / log 2)).add (hlog.div_const 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun k : ℕ ↦
      logb 2 R - ((1 / log 2) / k + (logb 2 k / k) / 2)) ?_ tendsto_const_nhds ?_ ?_
  · simpa using tendsto_const_nhds.sub herr
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have h := balanced_logb_lower hR hk (hfactorial k hk)
    apply (le_div_iff₀ (by positivity)).mpr
    convert h using 1
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hN : 0 < N k := by
      have h := hfactorial k hk
      exact Nat.pos_of_mul_pos_right (h ▸ Nat.factorial_pos _)
    have hc : (N k : ℝ) ≤ (R : ℝ) ^ (R * k) := by exact_mod_cast hcard k hk
    have h := logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hN) hc
    rw [logb_pow, Nat.cast_mul] at h
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)

end SpectralBooks
end LinearAlgebra
end OAI
