import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! # The weighted slices of Proposition 9.2

The coefficient of the digit exponent records an original output equation, and the
higher powers record the affine hyperplanes. The dense output coordinates need not be
supplied to the evaluator: one evaluation of the table and one stored offset suffice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Finset

/-- Exponent of the output coordinate with multiindex `ν` in base `b`. -/
def digitExponent {k : ℕ} (b : ℕ) (ν : Fin k → ℕ) : ℕ := Nat.ofDigits b (List.ofFn ν)

/-- The digit encoding is the exponent produced by Kronecker substitution. -/
theorem digitExponent_eq_sum {k b : ℕ} (ν : Fin k → ℕ) :
    digitExponent b ν = ∑ i, b ^ i.val * ν i := by
  induction k with
  | zero => simp [digitExponent]
  | succ k ih =>
    rw [digitExponent, List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ]
    rw [← digitExponent, ih, Finset.mul_sum]
    simp [pow_succ', mul_assoc]

/-- Each digit string of length `k` gives an exponent below `b^k`. -/
theorem digitExponent_lt {k b : ℕ} (hb : 1 < b) {ν : Fin k → ℕ} (hν : ∀ i, ν i < b) :
    digitExponent b ν < b ^ k := by
  have hd : ∀ v ∈ List.ofFn ν, v < b := by simpa using hν
  simpa [digitExponent] using Nat.ofDigits_lt_base_pow_length hb hd

/-- Distinct bounded multiindices have distinct slice exponents, also with leading zero digits. -/
theorem digitExponent_inj {k b : ℕ} (hb : 1 < b) {ν μ : Fin k → ℕ}
    (hν : ∀ i, ν i < b) (hμ : ∀ i, μ i < b) (he : digitExponent b ν = digitExponent b μ) :
    ν = μ :=
  List.ofFn_inj.mp <| Nat.ofDigits_inj_of_len_eq hb (by simp)
    (by simpa using hν) (by simpa using hμ) he

/-- One-variable slice through the output residuals `p` and affine constraints `ℓ`. -/
noncomputable def slicePolynomial {R : Type*} [CommRing R] {k s : ℕ} (b : ℕ)
    (p : MvPolynomial (Fin k) R) (ℓ : Fin s → R) : Polynomial R :=
  (∑ ν ∈ p.support, Polynomial.monomial (digitExponent b ν) (p.coeff ν)) +
    ∑ j, Polynomial.monomial (b ^ k + (j.val + 1)) (ℓ j)

private theorem support_lt {R : Type*} [CommRing R] {k b : ℕ}
    {p : MvPolynomial (Fin k) R} (hd : p.totalDegree < b) {ν : Fin k →₀ ℕ}
    (hν : ν ∈ p.support) (i : Fin k) : ν i < b :=
  ((MvPolynomial.monomial_le_degreeOf i hν).trans (MvPolynomial.degreeOf_le_totalDegree p i)).trans_lt hd

/-- Reading the coefficient at a bounded output exponent recovers the output equation. -/
theorem coeff_slice_output {R : Type*} [CommRing R] {k s b : ℕ} (hb : 1 < b)
    (p : MvPolynomial (Fin k) R) (hd : p.totalDegree < b) (ℓ : Fin s → R)
    {ν : Fin k →₀ ℕ} (hν : ν ∈ p.support) :
    (slicePolynomial b p ℓ).coeff (digitExponent b ν) = p.coeff ν := by
  classical
  simp only [slicePolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  have h₁ : ∀ j : Fin s, b ^ k + (j.val + 1) ≠ digitExponent b ν := by
    have := digitExponent_lt hb (support_lt hd hν)
    omega
  simp only [ite_eq_right (h₁ _), sum_const_zero, add_zero]
  rw [Finset.sum_eq_single_of_mem ν hν]
  · simp
  · intro μ hμ hne
    exact ite_eq_right (fun he ↦ hne (DFunLike.coe_injective
      (digitExponent_inj hb (support_lt hd hμ) (support_lt hd hν) he)))

/-- The disjoint high exponents recover each original affine constraint. -/
theorem coeff_slice_hyperplane {R : Type*} [CommRing R] {k s b : ℕ} (hb : 1 < b)
    (p : MvPolynomial (Fin k) R) (hd : p.totalDegree < b) (ℓ : Fin s → R) (j : Fin s) :
    (slicePolynomial b p ℓ).coeff (b ^ k + (j.val + 1)) = ℓ j := by
  classical
  simp only [slicePolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  have hzero : ∀ ν ∈ p.support, digitExponent b ν ≠ b ^ k + (j.val + 1) := by
    intro ν hν
    have := digitExponent_lt hb (support_lt hd hν)
    omega
  rw [Finset.sum_eq_zero (fun ν hν ↦ ite_eq_right (hzero ν hν)), zero_add]
  simp [← Fin.ext_iff]

/-- Nonzero original equations at a point give a nonzero exclusion polynomial in the slice scalar. -/
theorem slicePolynomial_ne_zero {R : Type*} [CommRing R] {k s b : ℕ} (hb : 1 < b)
    (p : MvPolynomial (Fin k) R) (hd : p.totalDegree < b) (ℓ : Fin s → R)
    (hne : p ≠ 0 ∨ ∃ j, ℓ j ≠ 0) : slicePolynomial b p ℓ ≠ 0 := by
  intro he
  rcases hne with hp | ⟨j, hj⟩
  · obtain ⟨ν, hν⟩ := MvPolynomial.support_nonempty.mpr hp
    have h := coeff_slice_output hb p hd ℓ hν
    rw [he, Polynomial.coeff_zero] at h
    exact (MvPolynomial.mem_support_iff.mp hν) h.symm
  · have h := coeff_slice_hyperplane hb p hd ℓ j
    rw [he, Polynomial.coeff_zero] at h
    exact hj h.symm

/-- The univariate bad-locus polynomial has degree at most `b^k+s`. -/
theorem natDegree_slicePolynomial_le {R : Type*} [CommRing R] {k s b : ℕ} (hb : 1 < b)
    (p : MvPolynomial (Fin k) R) (hd : p.totalDegree < b) (ℓ : Fin s → R) :
    (slicePolynomial b p ℓ).natDegree ≤ b ^ k + s := by
  apply (Polynomial.natDegree_add_le ..).trans (max_le ?_ ?_)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro ν hν
    exact (Polynomial.natDegree_monomial_le _).trans <|
      (digitExponent_lt hb (support_lt hd hν)).le.trans (Nat.le_add_right ..)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.add_le_add_left j.isLt _)

/-- The weighted coordinate sum is one evaluation of the multivariate polynomial. -/
theorem eval_at_digit_powers {R : Type*} [CommRing R] {k : ℕ} (b : ℕ)
    (a : R) (p : MvPolynomial (Fin k) R) :
    MvPolynomial.eval (fun i : Fin k ↦ a ^ (b ^ i.val)) p =
      ∑ ν ∈ p.support, p.coeff ν * a ^ digitExponent b ν := by
  rw [MvPolynomial.eval_eq']
  simp only [digitExponent_eq_sum, ← pow_mul, prod_pow_eq_pow_sum]

/-- Using one offset in the advice, the weighted output residuals are evaluated by a single
homogeneous-table evaluation, plus the affine corrections. -/
theorem eval_slice_with_offset {R : Type*} [CommRing R] {k s : ℕ} (b : ℕ) (a : R)
    (table prescribed : MvPolynomial (Fin k) R) (ℓ : Fin s → R) :
    (slicePolynomial b (table - prescribed) ℓ).eval a =
      MvPolynomial.eval (fun i : Fin k ↦ a ^ (b ^ i.val)) table -
      MvPolynomial.eval (fun i : Fin k ↦ a ^ (b ^ i.val)) prescribed +
      ∑ j, ℓ j * a ^ (b ^ k + (j.val + 1)) := by
  rw [slicePolynomial, Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [← eval_at_digit_powers, map_sub]

/-- For the manuscript's `2n` variables, every exponent below `B` fits in `2n²` bits. -/
theorem size_exponent_le {n e : ℕ} (he : e < (n + 1) ^ (2 * n)) :
    e.size ≤ 2 * n * n := by
  rw [Nat.size_le]
  apply he.trans_le
  calc
    _ ≤ (2 ^ n) ^ (2 * n) := Nat.pow_le_pow_left n.lt_two_pow_self _
    _ = _ := by rw [← pow_mul, mul_comm n (2 * n)]

end Branch

end BorderVNP
end Computability
end OAI
