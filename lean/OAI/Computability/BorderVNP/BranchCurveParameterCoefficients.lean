import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Separating the deformation parameter from the curve equations

The equations in the manuscript are polynomials in `(X,t)`; the eliminant
uses polynomials in `X` over `E[t]`. The change of representation preserves
evaluation and partial derivatives in the parameter coordinates. Both the
coefficient degrees in `t` and the total `X`-degree remain bounded by the
original total degree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {E σ : Type*} [Field E]

private theorem param_monomial (m : Option σ →₀ ℕ) (a : E) :
    optionEquivRight E σ (monomial m a) =
      monomial m.some (Polynomial.monomial (m none) a) := by
  rw [optionEquivRight_apply, aeval_monomial, Finsupp.prod_option_index]
  · rw [monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Option.elim_none, Option.elim_some, algebraMap_apply, Polynomial.algebraMap_eq,
      map_mul, map_pow, mul_assoc]
  · simp
  · intros; rw [pow_add]

private theorem transposed_coeff (f : MvPolynomial (Option σ) E) (m : σ →₀ ℕ) (n : ℕ) :
    ((optionEquivRight E σ f).coeff m).coeff n = ((optionEquivLeft E σ f).coeff n).coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial j a =>
    rw [param_monomial, optionEquivLeft_monomial]
    by_cases h : j.some = m <;> by_cases h' : j none = n <;>
      simp [coeff_monomial, Polynomial.coeff_monomial, h, h']
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp, hq]

/-- A coefficient polynomial in the deformation parameter has degree bounded
by the total degree of the original equation. -/
theorem parameter_coeff_natDegree_le (f : MvPolynomial (Option σ) E) (m : σ →₀ ℕ) :
    ((optionEquivRight E σ f).coeff m).natDegree ≤ f.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h : (optionEquivLeft E σ f).natDegree < n := by
    rw [natDegree_optionEquivLeft]
    exact (degreeOf_le_totalDegree _ _).trans_lt hn
  rw [transposed_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt h]
  rfl

/-- Viewing the deformation parameter as a scalar cannot increase total
degree in the remaining variables. -/
theorem parameter_totalDegree_le (f : MvPolynomial (Option σ) E) :
    (optionEquivRight E σ f).totalDegree ≤ f.totalDegree := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro m hm
  have h := (mem_support_iff.mp hm : (optionEquivRight E σ f).coeff m ≠ 0)
  let p := (optionEquivRight E σ f).coeff m
  have hn : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h
  rw [transposed_coeff] at hn
  exact (le_totalDegree (mem_support_iff.mpr hn)).trans (totalDegree_coeff_optionEquivLeft_le E σ f _)

/-- Partial differentiation in a coordinate commutes with moving the
deformation parameter to the coefficient ring. -/
theorem parameter_pderiv (f : MvPolynomial (Option σ) E) (j : σ) :
    pderiv j (optionEquivRight E σ f) = optionEquivRight E σ (pderiv (some j) f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp only [optionEquivRight_C, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, pderiv_mul, pderiv_mul, map_add, map_mul, map_mul, hp]
    congr 2
    cases i with
    | none => simp [pderiv_X]
    | some i =>
      by_cases e : i = j <;> simp [pderiv_X, e]

/-- The two representations agree under every field specialization, including
at values where the chosen chart denominator vanishes. -/
theorem eval_parameter_coefficients {L : Type*} [Field L] (φ : Polynomial E →+* L)
    (x : σ → L) (f : MvPolynomial (Option σ) E) :
    eval₂ φ x (optionEquivRight E σ f) =
      eval₂ (φ.comp Polynomial.C) (fun i => i.elim (φ Polynomial.X) x) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [optionEquivRight_C, eval₂_C, RingHom.comp_apply]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    cases i <;> simp only [map_mul, eval₂_mul, optionEquivRight_X_none,
      optionEquivRight_X_some, eval₂_C, eval₂_X, hp, Option.elim_some, Option.elim_none]

end Branch

end BorderVNP
end Computability
end OAI
