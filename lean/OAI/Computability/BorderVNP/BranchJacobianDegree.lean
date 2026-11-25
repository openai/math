import OAI.Computability.BorderVNP.BranchJacobian
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Weight

/-! # Clearing the Jacobian determinant on a rational chart

On the finite-parameter locus of Proposition 9.2 write every slice as `numᵢ / den`.
Clearing the derivative matrix gives a polynomial exceptional equation of degree
at most `2 h d` when the numerators and denominator have degree at most `d`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped Matrix

variable {K L ι σ : Type*} [Field K] [Field L] [Algebra K L]

/-- Partial differentiation does not increase total degree in any characteristic. -/
theorem pderiv_degree (i : σ) (p : MvPolynomial σ K) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro a ha
  rw [pderiv_monomial]
  refine (totalDegree_monomial_le ..).trans ((Finsupp.degree_mono ?_).trans (le_totalDegree ha))
  exact tsub_le_self

variable [Fintype ι] [DecidableEq ι]

/-- Polynomial numerator of the deformed derivative matrix before taking its determinant. -/
noncomputable def jacobianNumerator (t : K) (den : MvPolynomial ι K)
    (num : ι → MvPolynomial ι K) : Matrix ι ι (MvPolynomial ι K) :=
  Matrix.scalar ι (C t * den^2) + Matrix.of fun i j => den * pderiv j (num i) - num i * pderiv j den

/-- The quotient-rule derivative matrix evaluated at the chart coordinates. -/
noncomputable def rationalJacobianAt (z : ι → L) (den : MvPolynomial ι K)
    (num : ι → MvPolynomial ι K) : Matrix ι ι L :=
  Matrix.of fun i j => (aeval z den * aeval z (pderiv j (num i)) -
      aeval z (num i) * aeval z (pderiv j den)) / (aeval z den)^2

omit [Fintype ι] in
private theorem coordinate_derivative (z : ι → L) (D : Derivation K L L) (j : ι)
    (hD : ∀ i, D (z i) = if i = j then 1 else 0) (p : MvPolynomial ι K) :
    D (aeval z p) = aeval z (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C k => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    by_cases hi : i = j
    · subst i
      simp [D.leibniz, hp, hD, smul_eq_mul, mul_comm, add_comm]
    · simp [pderiv_X_of_ne hi, D.leibniz, hp, hD, hi, smul_eq_mul, mul_comm]

omit [Fintype ι] in
/-- The displayed quotient-rule matrix gives the actual coordinate derivations, for
every extension carrying these derivations, including in positive characteristic. -/
theorem derivation_rationalJacobianAt (z : ι → L) (D : Derivation K L L) (j : ι)
    (hD : ∀ i, D (z i) = if i = j then 1 else 0) (den : MvPolynomial ι K)
    (num : ι → MvPolynomial ι K) (i : ι) :
    D (aeval z (num i) / aeval z den) = rationalJacobianAt z den num i j := by
  rw [D.leibniz_div]
  simp only [smul_eq_mul, coordinate_derivative z D j hD, rationalJacobianAt,
    Matrix.of_apply, div_eq_mul_inv, inv_pow]
  ring

/-- Polynomial total degree of the cleared exceptional determinant in the chart variables. -/
theorem jacobianNumerator_det_degree (t : K) (den : MvPolynomial ι K) (num : ι → MvPolynomial ι K)
    {d : ℕ} (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d) :
    (jacobianNumerator t den num).det.totalDegree ≤ Fintype.card ι * (2*d) := by
  have hdd (j) : (pderiv j den).totalDegree ≤ d := (pderiv_degree j _).trans hd
  have hnd (i j) : (pderiv j (num i)).totalDegree ≤ d := (pderiv_degree j _).trans (hn i)
  have hentry (i j : ι) : (jacobianNumerator t den num i j).totalDegree ≤ 2*d := by
    apply (totalDegree_add ..).trans
    apply max_le
    · by_cases h : i = j
      · subst j
        simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
        apply (totalDegree_mul ..).trans
        rw [totalDegree_C, zero_add]
        exact (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ hd)
      · simp [Matrix.scalar, h]
    · apply (totalDegree_sub ..).trans
      rw [two_mul]
      exact max_le ((totalDegree_mul ..).trans (Nat.add_le_add hd (hnd i j)))
        ((totalDegree_mul ..).trans (Nat.add_le_add (hn i) (hdd j)))
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  apply (totalDegree_smul_le ..).trans
  refine (totalDegree_finsetProd ..).trans ?_
  exact (Finset.sum_le_sum (fun i _ => hentry (π i) i)).trans_eq (by simp)

/-- Evaluation of the cleared determinant agrees with the deformed rational Jacobian
up to the stated nonzero denominator power on the finite-parameter locus. -/
theorem aeval_jacobianNumerator_det (z : ι → L) (t : K) (den : MvPolynomial ι K)
    (num : ι → MvPolynomial ι K) (hd : aeval z den ≠ 0) :
    aeval z (jacobianNumerator t den num).det =
      (aeval z den ^ 2) ^ Fintype.card ι *
        (Matrix.scalar ι (algebraMap K L t) + rationalJacobianAt z den num).det := by
  rw [(aeval z).map_det, ← Matrix.det_smul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobianNumerator, rationalJacobianAt, Matrix.scalar, mul_add, mul_comm]
    rw [mul_comm ((aeval z den)^2), div_mul_cancel₀ _ (pow_ne_zero _ hd)]
  · simp [jacobianNumerator, rationalJacobianAt, Matrix.scalar, hij, mul_comm]
    rw [mul_comm ((aeval z den)^2), div_mul_cancel₀ _ (pow_ne_zero _ hd)]

end Branch

end BorderVNP
end Computability
end OAI
