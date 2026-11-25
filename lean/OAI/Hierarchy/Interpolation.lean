import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI
/-! # Homogeneous components by scalar interpolation

Evaluate at the same scalar dilation in every variable. A coefficient of
multi-degree `b` acquires the factor `t ^ b.degree`, so ordinary univariate
interpolation separates the total degrees in every characteristic.
-/

namespace Hierarchy
open MvPolynomial
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {σ : Type}

private theorem dilate_monomial (t : F) (b : σ →₀ ℕ) (r : F) :
    aeval (fun i => C t * X i) (monomial b r) = monomial b (t ^ b.degree * r) := by
  classical
  rw [aeval_monomial, monomial_eq]
  change C r * b.prod (fun i k => (C t * X i)^k) =
    C (t ^ b.degree * r) * b.prod (fun i k => X i ^ k)
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply, map_mul, map_pow]
  ring

theorem coeff_dilate (t : F) (p : MvPolynomial σ F) (b : σ →₀ ℕ) :
    (aeval (fun i => C t * X i) p).coeff b = t ^ b.degree * p.coeff b := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial k r =>
    rw [dilate_monomial]
    by_cases h : k = b
    · subst k
      simp
    · simp [coeff_monomial, h]
  | add p q hp hq => simp [hp, hq, mul_add]

private theorem interpolate_power (S : Finset F) (k d : ℕ) (small : k < S.card) :
    ∑ t ∈ S, (Lagrange.basis S id t).coeff d * t^k = if k=d then 1 else 0 := by
  classical
  let T := (Polynomial.X : Polynomial F)^k
  have hd : T.degree < S.card := by
    apply T.degree_le_natDegree.trans_lt
    exact_mod_cast (show T.natDegree < S.card by simpa [T] using small)
  have h := Lagrange.eq_interpolate (v := id) (s := S) Function.injective_id.injOn hd
  have c := congrArg (fun Q : Polynomial F => Q.coeff d) h
  simp only [T, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.eval_pow, Polynomial.eval_X, id_eq] at c
  simpa only [mul_comm, eq_comm] using c.symm

theorem homogeneousComponent_interpolation [Infinite F] (p : MvPolynomial σ F) (d m : ℕ)
    (hp : p.totalDegree ≤ m) :
    ∃ (S : Finset F) (c : F → F), S.card = m+1 ∧ homogeneousComponent d p =
      ∑ t ∈ S, C (c t) * aeval (fun i => C t * X i) p := by
  classical
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq F (m+1)
  refine ⟨S, fun t => (Lagrange.basis S id t).coeff d, hS, ?_⟩
  ext b
  simp only [coeff_homogeneousComponent, coeff_sum, coeff_C_mul, coeff_dilate]
  by_cases zero : p.coeff b = 0
  · simp [zero]
  have hb : b ∈ p.support := Finsupp.mem_support_iff.mpr zero
  have hdeg : b.degree ≤ p.totalDegree := MvPolynomial.le_totalDegree hb
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, interpolate_power S b.degree d (by omega)]
  split <;> simp_all


end
end Hierarchy

end OAI
