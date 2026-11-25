import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite weighted entropy inequality

The positive-parameter inequality is the weighted arithmetic--geometric mean
inequality applied to `c i ^ (1 / p) / q i`. Zero weights contribute the factor
one, and are treated before taking logarithms. The logarithmic AM--GM argument
below uses only `Real.log_le_sub_one_of_pos`.

The zero-parameter endpoint has a separate pointwise hypothesis: if every
`c i ≤ x`, then the weighted product is at most `x`.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open scoped BigOperators

private theorem fin_nonempty_of_probability_sum {s : ℕ} (q : Fin s → ℝ)
    (hqsum : ∑ i, q i = 1) : Nonempty (Fin s) := by
  cases s with
  | zero => simp at hqsum
  | succ s => exact ⟨0⟩

/-- The logarithmic weighted AM--GM inequality, with an upper bound on the
weighted arithmetic mean. The weights may vanish. -/
theorem weighted_log_le_log_of_sum_le {s : ℕ}
    (q a : Fin s → ℝ) (B : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (ha : ∀ i, 0 < a i) (hB : 0 < B)
    (hmean : ∑ i, q i * a i ≤ B) :
    ∑ i, q i * Real.log (a i) ≤ Real.log B := by
  have hterm (i : Fin s) :
      q i * (Real.log (a i) - Real.log B) ≤ q i * (a i / B - 1) := by
    simpa only [Real.log_div (ha i).ne' hB.ne'] using
      mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (ha i) hB)) (hq i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) =>
    hterm i)
  have hsum' :
      (∑ i, q i * Real.log (a i)) - Real.log B ≤
        (∑ i, q i * a i) / B - 1 := by
    simpa only [mul_sub, ← mul_div_assoc, mul_one, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hqsum, one_mul, ← Finset.sum_div] using hsum
  have hdiv : (∑ i, q i * a i) / B ≤ 1 :=
    (div_le_iff₀ hB).2 (by simpa only [one_mul] using hmean)
  linarith

/-- A product form of weighted AM--GM, proved from its logarithmic form. -/
theorem weighted_geometric_mean_le_of_sum_le {s : ℕ}
    (q a : Fin s → ℝ) (B : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (ha : ∀ i, 0 < a i) (hB : 0 < B)
    (hmean : ∑ i, q i * a i ≤ B) :
    ∏ i, (a i) ^ (q i) ≤ B := by
  apply (Real.log_le_log_iff
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (ha i) (q i))) hB).1
  calc
    Real.log (∏ i, (a i) ^ (q i)) = ∑ i, q i * Real.log (a i) := by
      rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (ha i) (q i)).ne')]
      exact Finset.sum_congr rfl (fun i _ => Real.log_rpow (ha i) (q i))
    _ ≤ Real.log B := weighted_log_le_log_of_sum_le q a B hq hqsum ha hB hmean

/-- The finite entropy/tag inequality for a positive real parameter.
The convention `x ^ (0 : ℝ) = 1` includes every zero weight. -/
theorem tag_entropy_product_le {s : ℕ}
    (p : ℝ) (c q : Fin s → ℝ)
    (hp : 0 < p) (hc : ∀ i, 0 < c i)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) :
    (∏ i, (c i / (q i) ^ p) ^ (q i)) ≤
      (∑ i, (c i) ^ (1 / p)) ^ p := by
  classical
  let a : Fin s → ℝ := fun i => if q i = 0 then 1 else (c i) ^ (1 / p) / q i
  let B : ℝ := ∑ i, (c i) ^ (1 / p)
  have ha : ∀ i, 0 < a i := by
    intro i
    by_cases hi : q i = 0
    · simp [a, hi]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      simpa only [a, ite_eq_right hi] using
        div_pos (Real.rpow_pos_of_pos (hc i) (1 / p)) hqi
  have : Nonempty (Fin s) := fin_nonempty_of_probability_sum q hqsum
  have hB : 0 < B :=
    Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hc i) (1 / p))
      Finset.univ_nonempty
  have hmean : ∑ i, q i * a i ≤ B := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i = 0
    · simpa only [hi, zero_mul] using (Real.rpow_pos_of_pos (hc i) (1 / p)).le
    · have hcancel : q i * a i = (c i) ^ (1 / p) := by
        simp only [a, ite_eq_right hi]
        field_simp [hi]
      exact hcancel.le
  have hlog := weighted_log_le_log_of_sum_le q a B hq hqsum ha hB hmean
  have hfactor_pos (i : Fin s) : 0 < (c i / (q i) ^ p) ^ (q i) := by
    by_cases hi : q i = 0
    · simp only [hi, Real.rpow_zero, zero_lt_one]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      exact Real.rpow_pos_of_pos
        (div_pos (hc i) (Real.rpow_pos_of_pos hqi p)) (q i)
  have hfactor_log (i : Fin s) :
      Real.log ((c i / (q i) ^ p) ^ (q i)) = p * (q i * Real.log (a i)) := by
    by_cases hi : q i = 0
    · simp [hi]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      rw [Real.log_rpow (div_pos (hc i) (Real.rpow_pos_of_pos hqi p)),
        Real.log_div (hc i).ne' (Real.rpow_pos_of_pos hqi p).ne',
        Real.log_rpow hqi p]
      simp only [a, ite_eq_right hi]
      rw [Real.log_div (Real.rpow_pos_of_pos (hc i) (1 / p)).ne' hqi.ne',
        Real.log_rpow (hc i) (1 / p)]
      field_simp [hp.ne']
  apply (Real.log_le_log_iff
    (Finset.prod_pos (fun i _ => hfactor_pos i)) (Real.rpow_pos_of_pos hB p)).1
  change Real.log (∏ i, (c i / (q i) ^ p) ^ (q i)) ≤ Real.log (B ^ p)
  rw [Real.log_prod (fun i _ => (hfactor_pos i).ne'), Real.log_rpow hB p]
  calc
    (∑ i, Real.log ((c i / (q i) ^ p) ^ (q i))) =
        p * (∑ i, q i * Real.log (a i)) := by
      simp_rw [hfactor_log]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ p * Real.log B := mul_le_mul_of_nonneg_left hlog hp.le

/-- Compose the entropy inequality with a bound on the optimized power sum. -/
theorem tag_entropy_product_le_of_bound {s : ℕ}
    (p x : ℝ) (c q : Fin s → ℝ)
    (hp : 0 < p) (hc : ∀ i, 0 < c i)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (hbound : (∑ i, (c i) ^ (1 / p)) ^ p ≤ x) :
    (∏ i, (c i / (q i) ^ p) ^ (q i)) ≤ x :=
  (tag_entropy_product_le p c q hp hc hq hqsum).trans hbound

/-- A weighted product of positive numbers is bounded by any pointwise upper
bound. This is the endpoint needed when the tag parameter is zero. -/
theorem weighted_geometric_mean_le_of_pointwise {s : ℕ}
    (c q : Fin s → ℝ) (x : ℝ)
    (hc : ∀ i, 0 < c i) (hq : ∀ i, 0 ≤ q i)
    (hqsum : ∑ i, q i = 1) (hcx : ∀ i, c i ≤ x) :
    (∏ i, (c i) ^ (q i)) ≤ x := by
  have : Nonempty (Fin s) := fin_nonempty_of_probability_sum q hqsum
  obtain ⟨i⟩ := ‹Nonempty (Fin s)›
  have hx : 0 < x := (hc i).trans_le (hcx i)
  apply weighted_geometric_mean_le_of_sum_le q c x hq hqsum hc hx
  calc
    (∑ i, q i * c i) ≤ ∑ i, q i * x :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcx i) (hq i))
    _ = x := by rw [← Finset.sum_mul, hqsum, one_mul]

/-- The zero-parameter tag inequality, in the same product notation as the
positive-parameter result. No limiting convention for `1 / p` is used. -/
theorem tag_entropy_product_zero_le {s : ℕ}
    (c q : Fin s → ℝ) (x : ℝ)
    (hc : ∀ i, 0 < c i) (hq : ∀ i, 0 ≤ q i)
    (hqsum : ∑ i, q i = 1) (hcx : ∀ i, c i ≤ x) :
    (∏ i, (c i / (q i) ^ (0 : ℝ)) ^ (q i)) ≤ x := by
  simpa only [Real.rpow_zero, div_one] using
    weighted_geometric_mean_le_of_pointwise c q x hc hq hqsum hcx

/-- Rewrite the quotient product as the exponential of the Shannon entropy
times the unnormalized weighted product. This identity also holds at `p = 0`
and at zero weights; it requires no normalization of the weights. -/
theorem tag_entropy_product_eq_exp {s : ℕ}
    (p : ℝ) (c q : Fin s → ℝ)
    (hc : ∀ i, 0 < c i) (hq : ∀ i, 0 ≤ q i) :
    (∏ i, (c i / (q i) ^ p) ^ (q i)) =
      Real.exp (p * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (c i) ^ (q i)) := by
  have hfactor_pos (i : Fin s) : 0 < (c i / (q i) ^ p) ^ (q i) := by
    by_cases hi : q i = 0
    · simp only [hi, Real.rpow_zero, zero_lt_one]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      exact Real.rpow_pos_of_pos
        (div_pos (hc i) (Real.rpow_pos_of_pos hqi p)) (q i)
  have hfactor_log (i : Fin s) :
      Real.log ((c i / (q i) ^ p) ^ (q i)) =
        q i * Real.log (c i) - p * (q i * Real.log (q i)) := by
    by_cases hi : q i = 0
    · simp [hi]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      rw [Real.log_rpow (div_pos (hc i) (Real.rpow_pos_of_pos hqi p)),
        Real.log_div (hc i).ne' (Real.rpow_pos_of_pos hqi p).ne',
        Real.log_rpow hqi p]
      ring
  have hcprod : 0 < ∏ i, (c i) ^ (q i) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hc i) (q i))
  apply Real.log_injOn_pos (Finset.prod_pos (fun i _ => hfactor_pos i))
    (mul_pos (Real.exp_pos _) hcprod)
  calc
    Real.log (∏ i, (c i / (q i) ^ p) ^ (q i)) =
        ∑ i, (q i * Real.log (c i) - p * (q i * Real.log (q i))) := by
      rw [Real.log_prod (fun i _ => (hfactor_pos i).ne')]
      exact Finset.sum_congr rfl (fun i _ => hfactor_log i)
    _ = p * (-(∑ i, q i * Real.log (q i))) +
        ∑ i, q i * Real.log (c i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = Real.log (Real.exp (p * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (c i) ^ (q i))) := by
      rw [Real.log_mul (Real.exp_pos _).ne' hcprod.ne', Real.log_exp,
        Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hc i) (q i)).ne')]
      congr 1
      exact (Finset.sum_congr rfl (fun i _ => Real.log_rpow (hc i) (q i))).symm

/-- The positive-parameter entropy inequality in exponential notation. -/
theorem tag_entropy_exp_le {s : ℕ}
    (p : ℝ) (c q : Fin s → ℝ)
    (hp : 0 < p) (hc : ∀ i, 0 < c i)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) :
    Real.exp (p * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (c i) ^ (q i)) ≤ (∑ i, (c i) ^ (1 / p)) ^ p := by
  rw [← tag_entropy_product_eq_exp p c q hc hq]
  exact tag_entropy_product_le p c q hp hc hq hqsum

/-- Compose the exponential entropy inequality with an optimized power-sum
bound, without further assumptions on the auxiliary parameter `x`. -/
theorem tag_entropy_exp_le_of_bound {s : ℕ}
    (p x : ℝ) (c q : Fin s → ℝ)
    (hp : 0 < p) (hc : ∀ i, 0 < c i)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (hbound : (∑ i, (c i) ^ (1 / p)) ^ p ≤ x) :
    Real.exp (p * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (c i) ^ (q i)) ≤ x :=
  (tag_entropy_exp_le p c q hp hc hq hqsum).trans hbound

/-- The zero-parameter endpoint in exponential entropy notation. -/
theorem tag_entropy_exp_zero_le {s : ℕ}
    (c q : Fin s → ℝ) (x : ℝ)
    (hc : ∀ i, 0 < c i) (hq : ∀ i, 0 ≤ q i)
    (hqsum : ∑ i, q i = 1) (hcx : ∀ i, c i ≤ x) :
    Real.exp ((0 : ℝ) * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (c i) ^ (q i)) ≤ x := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    weighted_geometric_mean_le_of_pointwise c q x hc hq hqsum hcx

end OAI.LinearAlgebra.TensorSpectrum
