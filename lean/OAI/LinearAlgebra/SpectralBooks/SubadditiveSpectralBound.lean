import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import OAI.LinearAlgebra.SpectralBooks.MultinomialExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Ordinary sums at the diagonal exponent

A multiplicative subadditive evaluation bounded by `n^p` on the positive
naturals satisfies the corresponding finite-sum bound with coefficient
`L^p`. In each power of the sum there are polynomially many exponent profiles.
Each multinomial coefficient costs at most `(L^p)^m`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset
open scoped NNReal

variable {A ι : Type*} [CommSemiring A] [Fintype ι] [Nonempty ι]
variable (v : A →* ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
  (hadd : ∀ x y, v (x + y) ≤ v x + v y)
  (hnat : ∀ n : ℕ, 0 < n → v (n : A) ≤ (n : ℝ≥0) ^ p)

omit [Nonempty ι] in
include hp hnat in
private theorem spectralMonomial_le (x : ι → A) {B : ℝ≥0} (hx : ∀ i, v (x i) ≤ B)
    {m : ℕ} {k : ι → ℕ} (hdeg : ∑ i, k i = m)
    (hcoeff : Nat.multinomial univ k ≤ Fintype.card ι ^ m) :
    v ((Nat.multinomial univ k : A) * ∏ i, (x i) ^ k i) ≤
      ((Fintype.card ι : ℝ≥0) ^ p * B) ^ m := by
  have hc := hnat _ (Nat.multinomial_pos univ k)
  have hcoef' : (Nat.multinomial univ k : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) ^ m := by
    exact_mod_cast hcoeff
  have hpow : ((Fintype.card ι : ℝ≥0) ^ m) ^ p = ((Fintype.card ι : ℝ≥0) ^ p)^m := by
    rw [← NNReal.rpow_natCast_mul, mul_comm (m : ℝ) p, NNReal.rpow_mul_natCast]
  have hprod : ∏ i, (v (x i)) ^ k i ≤ B ^ m := calc
    _ ≤ ∏ i, B ^ k i := Finset.prod_le_prod fun i _ => by gcongr; exact hx i
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hdeg]
  simp only [map_mul, map_prod, map_pow, mul_pow]
  exact mul_le_mul' (hc.trans ((NNReal.rpow_le_rpow hcoef' hp).trans_eq hpow)) hprod

include hp hadd hnat in
/-- A multiplicative subadditive evaluation pays at most the diagonal price
times the greatest summand value in every nonempty finite sum. -/
theorem subadditiveSpectral_sum_le (x : ι → A) {B : ℝ≥0} (hx : ∀ i, v (x i) ≤ B) :
    v (∑ i, x i) ≤ (Fintype.card ι : ℝ≥0) ^ p * B := by
  classical
  apply nnreal_le_of_pow_le_polynomial_mul_pow (Fintype.card ι)
  intro m _
  let profiles := (univ : Finset ι).piAntidiag m
  let term (k : ι → ℕ) := (Nat.multinomial univ k : A) * ∏ i, (x i)^k i
  have hcard : (profiles.card : ℝ≥0) ≤ ((m : ℝ≥0) + 1) ^ Fintype.card ι := by
    exact_mod_cast degreeProfiles_card_le (ι := ι) m
  calc
    v (∑ i, x i) ^ m = v (∑ k ∈ profiles, term k) := by
      rw [← map_pow, Finset.sum_pow_eq_sum_piAntidiag]
    _ ≤ ∑ k ∈ profiles, v (term k) :=
      Finset.le_sum_nonempty_of_subadditive v hadd (degreeProfiles_nonempty (ι := ι) m) term
    _ ≤ ∑ _k ∈ profiles, ((Fintype.card ι : ℝ≥0) ^ p * B) ^ m := by
      apply Finset.sum_le_sum
      intro k hk
      exact spectralMonomial_le v hp hnat x hx (Finset.mem_piAntidiag.mp hk).1
        (multinomial_le_wordCount hk)
    _ = (profiles.card : ℝ≥0) * ((Fintype.card ι : ℝ≥0) ^ p * B) ^ m := by simp
    _ ≤ _ := by gcongr

include hp hadd hnat in
/-- The binary case of the exact finite-sum bound. -/
theorem subadditiveSpectral_add_le (a b : A) :
    v (a + b) ≤ (2 : ℝ≥0) ^ p * max (v a) (v b) := by
  have h := subadditiveSpectral_sum_le v hp hadd hnat ![a, b] (B := max (v a) (v b)) (by
    intro i
    fin_cases i <;> simp)
  simpa [Fin.sum_univ_two] using h

include hp hadd hnat in
/-- Taking logarithms selects a positive summand at the diagonal price
`p * log₂ L`, including the case of a vanishing diagonal exponent. -/
theorem subadditiveSpectral_exists_logb_summand (x : ι → A) (hs : 0 < v (∑ i, x i)) :
    ∃ i, 0 < v (x i) ∧ Real.logb 2 (v (∑ j, x j)) ≤
      Real.logb 2 (v (x i)) + p * Real.logb 2 (Fintype.card ι) := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => v (x j)
  have h := subadditiveSpectral_sum_le v hp hadd hnat x hi
  have hi' : 0 < v (x i) := pos_of_mul_pos_right (hs.trans_le h) (by positivity)
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have h' : (v (∑ j, x j) : ℝ) ≤ (Fintype.card ι : ℝ) ^ p * (v (x i) : ℝ) := by
    exact_mod_cast h
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hs) h'
  rw [Real.logb_mul (Real.rpow_pos_of_pos hcard _).ne' (by exact_mod_cast hi'.ne'),
    Real.logb_rpow_eq_mul_logb_of_pos hcard, add_comm] at hlog
  exact ⟨i, hi', hlog⟩

end SpectralBooks
end LinearAlgebra
end OAI
