import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Highest coefficient on an affine line

Substitute `hᵢ + vᵢT` in a polynomial of total degree `d`. The resulting
polynomial in `T` has degree at most `d`, and its coefficient of `Tᵈ` is the
degree-`d` homogeneous component evaluated at the direction `v`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

variable {I E A : Type*} [CommSemiring E] [CommSemiring A] [Algebra E A]

/-- Restriction to the affine line through `h` with direction `v`. -/
noncomputable def line (p : MvPolynomial I E) (h : I → A) (v : I → E) : Polynomial A :=
  MvPolynomial.aeval (fun i => Polynomial.C (h i) + Polynomial.C (algebraMap E A (v i)) * Polynomial.X) p

private theorem top_product (s : Finset I) (f : I → Polynomial A) (d : I → ℕ)
    (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨hds, hcs⟩ := ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))
    have hdi := hd i (Finset.mem_insert_self i s)
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hdi hds),
      (Polynomial.coeff_mul_add_eq_of_natDegree_le hdi hds).trans (congrArg (_ * ·) hcs)⟩

private theorem line_monomial (e : I →₀ ℕ) (r : E) (h : I → A) (v : I → E) :
    (line (MvPolynomial.monomial e r) h v).natDegree ≤ e.degree ∧
    (line (MvPolynomial.monomial e r) h v).coeff e.degree =
      algebraMap E A (MvPolynomial.eval v (MvPolynomial.monomial e r)) := by
  let f (i : I) := Polynomial.C (h i) + Polynomial.C (algebraMap E A (v i)) * Polynomial.X
  have hf (i : I) : (f i).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le))
  have hc (i : I) : (f i).coeff 1 = algebraMap E A (v i) := by simp [f]
  have hfd (i : I) : (f i ^ e i).natDegree ≤ e i := by
    simpa using Polynomial.natDegree_pow_le_of_le (e i) (hf i)
  have hfc (i : I) : (f i ^ e i).coeff (e i) = algebraMap E A (v i) ^ e i := by
    simpa [hc] using Polynomial.coeff_pow_of_natDegree_le (m := e i) (hf i)
  obtain ⟨hdeg, hcoeff⟩ := top_product e.support (fun i => f i ^ e i) e (fun i _ => hfd i)
  simp only [line, MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod,
    Finsupp.degree_apply, MvPolynomial.eval_monomial, map_mul, map_prod, map_pow]
  exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans hdeg,
    by rw [Polynomial.coeff_C_mul, hcoeff]; simp_rw [hfc]⟩

private theorem line_eq_sum (p : MvPolynomial I E) (h : I → A) (v : I → E) :
    line p h v = ∑ e ∈ p.support, line (MvPolynomial.monomial e (p.coeff e)) h v := by
  unfold line
  conv_lhs => rw [p.as_sum, map_sum]

/-- Restriction to an affine line cannot increase the total degree. -/
theorem natDegree_line_le (p : MvPolynomial I E) (h : I → A) (v : I → E) :
    (line p h v).natDegree ≤ p.totalDegree := by
  rw [line_eq_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he =>
    (line_monomial e _ h v).1.trans (MvPolynomial.le_totalDegree he)

/-- Only the top homogeneous component contributes to the coefficient of the
highest possible power of the line parameter. -/
theorem coeff_line_totalDegree (p : MvPolynomial I E) (h : I → A) (v : I → E) :
    (line p h v).coeff p.totalDegree =
      algebraMap E A (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) := by
  classical
  rw [line_eq_sum, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply,
    map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  by_cases hd : e.degree = p.totalDegree
  · simpa only [hd, ite_true] using (line_monomial e (p.coeff e) h v).2
  · rw [ite_eq_right hd]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((line_monomial e _ h v).1.trans_lt
      (lt_of_le_of_ne (MvPolynomial.le_totalDegree he) hd))

end LinearNormalization

end VPVNP
end Computability
end OAI
