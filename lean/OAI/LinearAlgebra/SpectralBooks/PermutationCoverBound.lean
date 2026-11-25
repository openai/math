import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith

/-! # Probability estimate for covering ordered pairs by permutations -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The number of independent permutations used in Lemma `lem:stretch`
makes the union bound over all ordered pairs strictly less than one. -/
theorem missedPairs_lt_one (N : ℕ) (hN : 0 < N) :
    (N : ℝ)^2 * (1 - 1 / (N : ℝ))^(⌈3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ))⌉₊) < 1 := by
  let M := ⌈3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ))⌉₊
  change (N : ℝ)^2 * (1 - 1 / (N : ℝ))^M < 1
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hn'
  have hlogb : Real.log 2 + Real.log N ≤ Real.logb 2 (2 * (N : ℝ)) := by
    rw [Real.logb, Real.log_mul (by norm_num) hn.ne']
    apply (le_div_iff₀ hlog2).2
    exact mul_le_of_le_one_right (by positivity) hlog2'
  have hexp : 2 * Real.log N < (M : ℝ) / N := by
    apply (lt_div_iff₀ hn).2
    calc
      2 * Real.log N * N < 3 * (N : ℝ) * (Real.log 2 + Real.log N) := by
        nlinarith [mul_pos hn hlog2, mul_nonneg hn.le hlog]
      _ ≤ 3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ)) := by gcongr
      _ ≤ (M : ℝ) := Nat.le_ceil _
  have hbase : 0 ≤ 1 - 1 / (N : ℝ) := sub_nonneg.mpr ((div_le_one hn).mpr hn')
  calc
    (N : ℝ)^2 * (1 - 1 / (N : ℝ))^M ≤
        (N : ℝ)^2 * (Real.exp (-(1 / (N : ℝ))))^M := by
      gcongr
      linarith [Real.add_one_le_exp (-(1 / (N : ℝ)))]
    _ = Real.exp (Real.log ((N : ℝ)^2) - (M : ℝ) / N) := by
      rw [← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
      congr 2
      ring
    _ < 1 := by
      rw [Real.exp_lt_one_iff, Real.log_pow]
      norm_num at *
      linarith

/-- For words of length `m` on `R` letters, the base-two logarithm of the
union-bound list size exceeds `m * logb 2 R` by at most a logarithmic term. -/
theorem permutationCover_logb_le {R m N M : ℕ}
    (hR : 0 < R) (hm : 0 < m) (hN : 0 < N) (hM : 0 < M)
    (hwords : N ≤ R^m) (hcover : M ≤ ⌈3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ))⌉₊) :
    Real.logb 2 M ≤ m * Real.logb 2 R + Real.logb 2 (4 * (1 + Real.logb 2 R)) +
      Real.logb 2 m := by
  have base : (1 : ℝ) < 2 := by norm_num
  have hR1 : 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogR := Real.logb_nonneg base hR1
  have hlogN := Real.logb_nonneg base hn1
  have hnle : (N : ℝ) ≤ (R : ℝ)^m := by exact_mod_cast hwords
  have hlogs := Real.logb_le_logb_of_le base (by positivity) hnle
  rw [Real.logb_pow] at hlogs
  have htwice : Real.logb 2 (2 * (N : ℝ)) = 1 + Real.logb 2 N := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * (N : ℝ) * (1 + Real.logb 2 N))
  rw [htwice] at hcover
  have hM' : (M : ℝ) ≤ ⌈3 * (N : ℝ) * (1 + Real.logb 2 N)⌉₊ := by exact_mod_cast hcover
  have hfactor : 1 + Real.logb 2 N ≤ (1 + Real.logb 2 R) * m := by linarith
  have hMle : (M : ℝ) ≤ (R : ℝ)^m * (4 * (1 + Real.logb 2 R)) * m := by
    calc
      (M : ℝ) ≤ 3 * (N : ℝ) * (1 + Real.logb 2 N) + 1 := (hM'.trans hceil.le)
      _ ≤ 4 * (N : ℝ) * (1 + Real.logb 2 N) := by nlinarith [mul_nonneg (Nat.cast_nonneg N) hlogN]
      _ ≤ 4 * (R : ℝ)^m * ((1 + Real.logb 2 R) * m) :=
        mul_le_mul (by gcongr) hfactor (by positivity) (by positivity)
      _ = _ := by ring
  have h := Real.logb_le_logb_of_le base (by positivity) hMle
  rwa [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow] at h

open Filter
open scoped Topology

/-- The logarithmic overhead in the permutation-cover bound vanishes after
normalization by word length for every fixed alphabet size. -/
theorem tendsto_permutationCover_error (R : ℕ) :
    Tendsto (fun m : ℕ ↦ (Real.logb 2 (4 * (1 + Real.logb 2 R)) + Real.logb 2 m) / m)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.logb 2 m / m) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [add_div, add_zero] using
    (tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 (4 * (1 + Real.logb 2 R)))).add hlog

end SpectralBooks
end LinearAlgebra
end OAI
