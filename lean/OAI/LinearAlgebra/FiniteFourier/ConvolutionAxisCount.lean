import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Counting distinct axes from their product

Distinct positive axis lengths have product at least the factorial of their
number. Inverting this estimate bounds the number of axes in a box of volume
at most `n`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

/-- The product of distinct positive integers is at least their count factorial. -/
theorem factorial_card_le_prod (s : Finset ℕ) (hpos : ∀ x ∈ s, 0 < x) :
    s.card.factorial ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => (lt_irrefl a) (ha a h)
    have hsub : insert a s ⊆ Finset.Icc 1 a := by
      intro x hx
      refine Finset.mem_Icc.mpr ⟨hpos x hx, ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | h
      · exact le_rfl
      · exact (ha _ h).le
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem has, Nat.card_Icc] at hc
    rw [Finset.card_insert_of_notMem has, Nat.factorial_succ, Finset.prod_insert has]
    exact Nat.mul_le_mul (by omega) (ih fun x hx => hpos x (Finset.mem_insert_of_mem hx))

/-- An explicit uniform bound on the inverse factorial, using natural logarithms. -/
theorem axisCount_le_log_div_loglog {d n : ℕ} (hn : 3 ≤ n) (h : d.factorial ≤ n) :
    (d : ℝ) ≤ 9 * Real.log n / Real.log (Real.log n) := by
  have hlog : 1 < Real.log n := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < (n : ℝ))).mpr
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  apply (le_div_iff₀ (Real.log_pos hlog)).mpr
  by_cases hd : d ≤ 9
  · have hd' : (d : ℝ) ≤ 9 := by exact_mod_cast hd
    exact mul_le_mul hd' (Real.log_le_self (by linarith)) (Real.log_pos hlog).le (by norm_num)
  have hd' : 9 ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hd)
  have hld : 2 ≤ Real.log d := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < (d : ℝ))).mpr
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    exact (mul_le_mul Real.exp_one_lt_three.le Real.exp_one_lt_three.le
      (Real.exp_pos _).le (by norm_num)).trans (by linarith)
  have hfac : Real.log (d.factorial : ℝ) ≤ Real.log n := by
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos d) (by exact_mod_cast h)
  have hst := Stirling.le_log_factorial_stirling (n := d) (by omega)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hmain : (d : ℝ) * Real.log d ≤ 2 * Real.log n := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity) (sub_nonneg.mpr hld)]
  by_cases hx : Real.log n ≤ (d : ℝ) ^ 2
  · have hll := Real.log_le_log (by linarith : 0 < Real.log n) hx
    rw [Real.log_pow, Nat.cast_ofNat] at hll
    nlinarith [mul_le_mul_of_nonneg_left hll (show 0 ≤ (d : ℝ) by positivity)]
  · have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log n)
    have hds : (d : ℝ) ≤ Real.sqrt (Real.log n) := by
      nlinarith [Real.sqrt_nonneg (Real.log n)]
    have hls : Real.log (Real.log n) ≤ 2 * Real.sqrt (Real.log n) := by
      have hh := Real.log_le_self (Real.sqrt_pos.mpr (by linarith : 0 < Real.log n)).le
      rw [Real.log_sqrt (by linarith)] at hh
      linarith
    nlinarith [mul_le_mul hds hls (Real.log_pos hlog).le (Real.sqrt_nonneg _)]

end FiniteFourier
end LinearAlgebra
end OAI
