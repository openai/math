import OAI.LinearAlgebra.FiniteFourier.WeightedCoefficients
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Removing the Taylor-coefficient weights at evaluation

The tensor power of an entrywise degree-`d` polynomial matrix has degree at most
`d * k`. Summing its coefficients costs a polynomial factor in `k`, which
disappears on taking the exponential growth rate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators
open Polynomial

section

variable {K ι : Type*} [Field K]

private theorem slotPower_eval_one_sum (Q : ι → K[X]) (d : ℕ)
    (hQ : ∀ x, (Q x).natDegree ≤ d) (k : ℕ) :
    slotPower (fun z => (Q z).eval 1) k =
      ∑ i ∈ Finset.range (d * k + 1), powerCoeff (fun z => (Q z : PowerSeries K)) k i := by
  classical
  funext x
  let f := ∏ j, Q (x j)
  have hdeg : f.natDegree ≤ d * k := calc
    f.natDegree ≤ ∑ j, (Q (x j)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _ : Fin k, d := Finset.sum_le_sum fun j _ => hQ (x j)
    _ = d * k := by simp [Nat.mul_comm]
  have hf := congrArg (Polynomial.eval (1 : K)) (f.as_sum_range' _ (Nat.lt_succ_of_le hdeg))
  have hmap : (f : PowerSeries K) = ∏ j, (Q (x j) : PowerSeries K) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := K)) _ _
  simp only [Finset.sum_apply, powerCoeff, slotPower, ← hmap, Polynomial.coeff_coe]
  simpa only [f, Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one,
    Polynomial.eval_prod] using hf

/-- Evaluating at one costs at most one factor `w⁻¹` per polynomial degree
relative to a weighted bound on the coefficients of all powers. -/
theorem polynomialValue_of_weightedBound (ν : TensorValue K ι) (Q : ι → K[X]) (d : ℕ)
    (hQ : ∀ x, (Q x).natDegree ≤ d) {w M : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hM : 0 ≤ M)
    (h : WeightedBound ν w M (fun z => (Q z : PowerSeries K))) :
    ν.price 1 (slotPower (fun z => (Q z).eval 1) 1) ≤ w⁻¹ ^ d * M := by
  classical
  obtain ⟨q, hq⟩ := h
  apply OAI.LinearAlgebra.SpectralBooks.le_of_pow_le_polynomial_mul_pow
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hw.le) _) hM) ((d + 1) * (q + 1))
  intro k _
  let B := ((k : ℝ) + 1) ^ (d + 1)
  have hB : (k : ℝ) + d * k + 1 ≤ B := by
    calc
      (k : ℝ) + d * k + 1 = 1 + (↑(d + 1) : ℝ) * k := by push_cast; ring
      _ ≤ (1 + (k : ℝ)) ^ (d + 1) :=
        one_add_mul_le_pow (by linarith [Nat.cast_nonneg (α := ℝ) k]) _
      _ = B := by rw [add_comm 1]
  let coeffs := powerCoeff (fun z => (Q z : PowerSeries K)) k
  have hcoeff (i : ℕ) (hi : i ≤ d * k) :
      ν.price k (coeffs i) ≤ B ^ q * (w⁻¹ ^ d * M) ^ k := by
    have hi' : (i : ℝ) ≤ d * k := by exact_mod_cast hi
    have hprice := (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hw.le hw1 hi) (ν.nonneg (coeffs i))).trans (hq k i)
    have hpoly := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k + i + 1)
      (show (k : ℝ) + i + 1 ≤ B by linarith) q
    have hh := hprice.trans (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hM k))
    calc
      _ = (w ^ (d * k))⁻¹ * (w ^ (d * k) * ν.price k (coeffs i)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw.ne'), one_mul]
      _ ≤ (w ^ (d * k))⁻¹ * (B ^ q * M ^ k) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [mul_pow, ← pow_mul, inv_pow]; ring
  rw [← ν.power, slotPower_eval_one_sum Q d hQ k]
  calc
    _ ≤ ∑ i ∈ Finset.range (d * k + 1), ν.price k (coeffs i) := ν.price_sum _ _
    _ ≤ ∑ _i ∈ Finset.range (d * k + 1), B ^ q * (w⁻¹ ^ d * M) ^ k :=
      Finset.sum_le_sum fun i hi => hcoeff i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = (↑(d * k + 1) : ℝ) * (B ^ q * (w⁻¹ ^ d * M) ^ k) := by simp
    _ ≤ B * (B ^ q * (w⁻¹ ^ d * M) ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [B]; positivity)
      push_cast
      linarith
    _ = _ := by rw [pow_mul, pow_succ]; dsimp [B]; ring

end

end FiniteFourier
end LinearAlgebra
end OAI
