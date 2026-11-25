import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The power law for a monotone multiplicative function

On the positive integers, a multiplicative, monotone real-valued function with
`1 ≤ f n ≤ n` is a real power.  No power representation is an input.  The proof
compares `n ^ k` with two successive powers of `m`; the resulting bounded error
forces the logarithmic slopes to agree by the Archimedean property.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

private theorem positiveNat_map_pow
    (f : ℕ → ℝ) (hone : f 1 = 1)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simpa using hone
  | succ k ih =>
      rw [pow_succ, hmul (n ^ k) n (Nat.one_le_pow k n (by omega)) hn,
        ih, pow_succ]

/-- Monotonicity and multiplicativity force equal logarithmic slopes.
The orientation here is useful without dividing by either logarithm. -/
theorem monotone_multiplicative_log_cross_le
    (f : ℕ → ℝ) (hone : f 1 = 1)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → f m ≤ f n)
    (hlower : ∀ n : ℕ, 1 ≤ n → 1 ≤ f n)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) :
    Real.log (f n) * Real.log (m : ℝ) ≤
      Real.log (f m) * Real.log (n : ℝ) := by
  have hm1 : 1 ≤ m := hm.le
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hfn : 0 < f n := lt_of_lt_of_le zero_lt_one (hlower n hn)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm)
  have hlogfm : 0 ≤ Real.log (f m) := Real.log_nonneg (hlower m hm1)
  have hbounded (k : ℕ) :
      (k : ℝ) * (Real.log (f n) * Real.log (m : ℝ) -
        Real.log (f m) * Real.log (n : ℝ)) ≤
      Real.log (f m) * Real.log (m : ℝ) := by
    obtain ⟨j, hjlower, hjupper⟩ :=
      exists_nat_pow_near (Nat.one_le_pow k n (by omega)) hm
    have hpower_lower : (m : ℝ) ^ j ≤ (n : ℝ) ^ k := by
      exact_mod_cast hjlower
    have hlogs_lower : (j : ℝ) * Real.log (m : ℝ) ≤
        (k : ℝ) * Real.log (n : ℝ) := by
      simpa only [Real.log_pow] using
        Real.log_le_log (pow_pos hmR j) hpower_lower
    have hvalues : f n ^ k ≤ f m ^ (j + 1) := by
      rw [← positiveNat_map_pow f hone hmul n hn k,
        ← positiveNat_map_pow f hone hmul m hm1 (j + 1)]
      exact hmono (n ^ k) (m ^ (j + 1))
        (Nat.one_le_pow k n (by omega)) hjupper.le
    have hlogs_upper : (k : ℝ) * Real.log (f n) ≤
        ((j : ℝ) + 1) * Real.log (f m) := by
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using
        Real.log_le_log (pow_pos hfn k) hvalues
    have h₁ := mul_le_mul_of_nonneg_right hlogs_upper hlogm.le
    have h₂ := mul_le_mul_of_nonneg_right hlogs_lower hlogfm
    nlinarith
  by_contra hnot
  have hpositive : 0 < Real.log (f n) * Real.log (m : ℝ) -
      Real.log (f m) * Real.log (n : ℝ) := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨k, hk⟩ := exists_lt_nsmul hpositive
    (Real.log (f m) * Real.log (m : ℝ))
  rw [nsmul_eq_mul] at hk
  exact (not_lt_of_ge (hbounded k)) hk

/-- Every monotone multiplicative function between `1` and the identity on the
positive natural numbers has a single exponent in `[0,1]`.  There is no
restriction on its unused value at zero. -/
theorem exists_power_of_monotone_multiplicative
    (f : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → f m ≤ f n)
    (hbound : ∀ n : ℕ, 1 ≤ n → 1 ≤ f n ∧ f n ≤ (n : ℝ)) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ ∀ n : ℕ, 1 ≤ n → f n = (n : ℝ) ^ p := by
  have hone : f 1 = 1 := by
    have h := hbound 1 le_rfl
    exact le_antisymm (by simpa using h.2) h.1
  have hlower : ∀ n : ℕ, 1 ≤ n → 1 ≤ f n := fun n hn => (hbound n hn).1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hf2pos : 0 < f 2 := lt_of_lt_of_le zero_lt_one (hlower 2 (by omega))
  have hf2log : 0 ≤ Real.log (f 2) := Real.log_nonneg (hlower 2 (by omega))
  have hf2upper : Real.log (f 2) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log hf2pos (by simpa using (hbound 2 (by omega)).2)
  refine ⟨Real.log (f 2) / Real.log (2 : ℝ), div_nonneg hf2log hlog2.le,
    (div_le_one hlog2).2 hf2upper, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.one_rpow, hone]
  have hn2 : 1 < n := by omega
  have hleft := monotone_multiplicative_log_cross_le f hone hmul hmono hlower
    n 2 hn (by omega)
  have hright := monotone_multiplicative_log_cross_le f hone hmul hmono hlower
    2 n (by omega) hn2
  have hcross : Real.log (f n) * Real.log (2 : ℝ) =
      Real.log (f 2) * Real.log (n : ℝ) := by
    exact le_antisymm (by simpa using hleft) (by simpa using hright)
  have hlog : Real.log (f n) =
      Real.log (n : ℝ) * (Real.log (f 2) / Real.log (2 : ℝ)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hlog2.ne').2
    simpa only [mul_comm] using hcross
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfn : 0 < f n := lt_of_lt_of_le zero_lt_one (hlower n hn)
  rw [Real.rpow_def_of_pos hnR, ← hlog, Real.exp_log hfn]

end OAI.LinearAlgebra.TensorSpectrum
