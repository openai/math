import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! ## The double counting estimate for dissociated minors

The input inequality counts subsets of subset products. Both exponent comparisons are first
made among natural numbers, before taking a base-two logarithm to express the paper's bound.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The first logarithm of the coefficient-counting inequality, with its upper bound kept
in an integer-power form. -/
theorem two_pow_le_of_subset_product_count {N s : ℕ} (hN : 1 ≤ N) (hs : s ≤ (N + 1)^6)
    (hcount : (2 : ℕ)^(2^s) ≤ (2^(s+1) * N.factorial^s + 1)^((N*s+1)^(N^2))) :
    (2 : ℕ)^s ≤ (N+1)^(7*N^2+8) := by
  have hfac : N.factorial ≤ 2^(N^2) := calc
    N.factorial ≤ N^N := Nat.factorial_le_pow N
    _ ≤ (2^N)^N := Nat.pow_le_pow_left N.lt_two_pow_self.le N
    _ = _ := by rw [← pow_mul, pow_two]
  have hD : 1 ≤ (N+1)^6 := pow_pos (Nat.succ_pos N) 6
  have hbase : 2^(s+1) * N.factorial^s + 1 ≤ 2^((N+1)^8) := by
    let k := s + 1 + N^2*s
    have hk : 2^(s+1) * N.factorial^s ≤ 2^k := calc
      _ ≤ 2^(s+1) * (2^(N^2))^s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfac _)
      _ = _ := by rw [← pow_mul, ← pow_add]
    have hpos : 0 < 2^k := by positivity
    have he : k+1 ≤ (N+1)^6 * (N^2+3) := by
      dsimp only [k]
      nlinarith [Nat.mul_le_mul_left (N^2) hs]
    have hquad : N^2+3 ≤ (N+1)^2 := by nlinarith
    calc
      _ ≤ 2^k + 2^k := by omega
      _ = 2^(k+1) := by rw [pow_succ]; omega
      _ ≤ 2^((N+1)^6 * (N^2+3)) := Nat.pow_le_pow_right (by decide) he
      _ ≤ 2^((N+1)^6 * (N+1)^2) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hquad)
      _ = _ := by rw [← pow_add]
  have hmon : N*s+1 ≤ (N+1)^7 := by
    calc
      N*s+1 ≤ N*(N+1)^6+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) _
      _ ≤ N*(N+1)^6+(N+1)^6 := Nat.add_le_add_left hD _
      _ = _ := by ring
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    _ ≤ _ := hcount
    _ ≤ (2^((N+1)^8))^((N*s+1)^(N^2)) := Nat.pow_le_pow_left hbase _
    _ ≤ (2^((N+1)^8))^(((N+1)^7)^(N^2)) :=
      Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_left hmon _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, Nat.add_comm 8]

/-- The arithmetic conclusion of Lemma 3.1 for a dissociated collection of size at most
`(N+1)^6`. -/
theorem log_bound_of_subset_product_count {N s : ℕ} (hN : 1 ≤ N) (hs : s ≤ (N + 1)^6)
    (hcount : (2 : ℕ)^(2^s) ≤ (2^(s+1) * N.factorial^s + 1)^((N*s+1)^(N^2))) :
    (s : ℝ) ≤ (7*(N : ℝ)^2+8) * Real.logb 2 (N+1) := by
  have h : (2 : ℝ)^s ≤ ((N : ℝ)+1)^(7*N^2+8 : ℕ) := by
    exact_mod_cast two_pow_le_of_subset_product_count hN hs hcount
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) h
  simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] using hl

/-- The cutoff at `(N+1)^6` is strictly larger than the final logarithmic bound. -/
theorem log_bound_lt_cutoff (N : ℕ) :
    (7*(N : ℝ)^2+8) * Real.logb 2 (N+1) < ((N:ℝ)+1)^6 := by
  have hr : (N:ℝ) + 1 ≤ (2:ℝ)^N := by exact_mod_cast N.lt_two_pow_self
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) hr
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at hl
  calc
    _ ≤ (7*(N:ℝ)^2+8)*N := mul_le_mul_of_nonneg_left hl (by positivity)
    _ < _ := by
      cases N with
      | zero => norm_num
      | succ n =>
        push_cast
        have hn : 0 ≤ (n:ℝ) := by positivity
        ring_nf
        nlinarith [show 0 ≤ (n:ℝ)^3 by positivity, show 0 ≤ (n:ℝ)^4 by positivity,
          show 0 ≤ (n:ℝ)^5 by positivity, show 0 ≤ (n:ℝ)^6 by positivity]

/-- It is sufficient to count subsets up to the cutoff: a larger family would have a
subset of cardinality exactly the cutoff, whose logarithmic bound is strictly smaller. -/
theorem log_bound_of_subset_counts {ι : Type*} {N : ℕ} (hN : 1 ≤ N) (J : Finset ι)
    (hcount : ∀ t ⊆ J, t.card ≤ (N+1)^6 →
      (2 : ℕ)^(2^t.card) ≤ (2^(t.card+1) * N.factorial^t.card + 1)^((N*t.card+1)^(N^2))) :
    (J.card : ℝ) ≤ (7*(N:ℝ)^2+8) * Real.logb 2 (N+1) := by
  have hcut : J.card < (N+1)^6 := by
    by_contra! hlarge
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hlarge
    have hsmall := log_bound_of_subset_product_count hN hcard.le (hcount t ht hcard.le)
    rw [hcard] at hsmall
    have hs : ((N:ℝ)+1)^6 ≤ (7*(N:ℝ)^2+8) * Real.logb 2 (N+1) := by
      exact_mod_cast hsmall
    exact (log_bound_lt_cutoff N).not_ge hs
  exact log_bound_of_subset_product_count hN hcut.le (hcount J (Finset.Subset.refl _) hcut.le)

/-- The proxy precision chosen in Section 3 loses at most one quarter of a bit on a
signed subset of at most `(N+1)^6` terms. -/
theorem proxy_error_at_cutoff (N : ℕ) :
    4 * ((N:ℝ)+1)^6 * (1 / 2^(100*(N+1)^3+7 : ℕ)) ≤ 1 := by
  have hlin : N+1 ≤ 2^N := N.lt_two_pow_self
  have hexp : 2 + N * 6 ≤ 100*(N+1)^3+7 := by
    nlinarith [show 0 ≤ N^3 by positivity, show 0 ≤ N^2 by positivity]
  have hnat : 4*(N+1)^6 ≤ 2^(100*(N+1)^3+7) := calc
    4*(N+1)^6 ≤ 4*(2^N)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlin _)
    _ = 2^(2+N*6) := by rw [pow_add, pow_mul]; norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp
  have hreal : 4*((N:ℝ)+1)^6 ≤ 2^(100*(N+1)^3+7 : ℕ) := by exact_mod_cast hnat
  rw [mul_one_div, div_le_one (by positivity)]
  exact hreal

end Compression
end LinearProgramming
end Optimization
end OAI
