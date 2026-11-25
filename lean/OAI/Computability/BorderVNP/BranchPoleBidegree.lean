import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! # Separate degree bounds for determinant eliminants

A matrix entry has bounded degree in the slice value and in the parameter, separately.
Swapping the two polynomial variables reduces both determinant estimates to the same
univariate estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Polynomial

/-- Swapping the two variables interchanges the two coefficient indices. -/
theorem swap_coeff_coeff {K : Type*} [CommSemiring K] (p : Polynomial (Polynomial K)) (i j : ℕ) :
    ((Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simpa [map_add, coeff_add] using congrArg₂ (· + ·) ha hb
    | monomial n a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hm : m = j <;> by_cases hn : n = i <;> simp [coeff_monomial, hm, hn]

/-- Coefficient degree bounds are outer degree bounds after exchanging the variables. -/
theorem swap_degree_le_iff {K : Type*} [CommSemiring K] (p : Polynomial (Polynomial K)) (d : ℕ) :
    (Bivariate.swap p).natDegree ≤ d ↔ ∀ j, (p.coeff j).natDegree ≤ d := by
  simp only [natDegree_le_iff_coeff_eq_zero]
  constructor
  · intro h j i hi
    rw [← swap_coeff_coeff, h i hi, coeff_zero]
  · intro h i hi
    ext j
    rw [swap_coeff_coeff, h j i hi, coeff_zero]

/-- The outer degree of a determinant is bounded by the matrix order times the entry bound. -/
theorem natDegree_det_le {K : Type*} [CommRing K] {r d : ℕ}
    (M : Matrix (Fin r) (Fin r) (Polynomial K)) (h : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ r * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le ..).trans
  simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ h (σ i) i)

/-- The parameter degrees of the determinant coefficients have the same bound. -/
theorem coeff_natDegree_det_le {K : Type*} [CommRing K] {r d : ℕ}
    (M : Matrix (Fin r) (Fin r) (Polynomial (Polynomial K)))
    (h : ∀ i j k, ((M i j).coeff k).natDegree ≤ d) (k : ℕ) :
    (M.det.coeff k).natDegree ≤ r * d := by
  apply (swap_degree_le_iff _ _).mp _ k
  rw [show Bivariate.swap M.det = (M.map Bivariate.swap).det from
    Bivariate.swap.toRingHom.map_det M]
  apply natDegree_det_le
  exact fun i j ↦ (swap_degree_le_iff _ _).mpr (h i j)

end Branch

end BorderVNP
end Computability
end OAI
