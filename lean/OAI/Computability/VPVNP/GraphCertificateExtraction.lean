import OAI.Computability.VPVNP.NullstellensatzGraph
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Bounded certificates from a monic graph relation

Replace the normalized graph coordinates by their linear parts. The difference
between the two substitutions is an explicit combination of the equations.
Its multipliers grow in degree by at most the maximum substitution degree for
each variable in a monomial. Taking the leading power of the graph parameter
then produces a certificate for one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

variable {E I V W : Type*} [Field E] [Fintype I]

private theorem bounded_substitution_difference
    (F : I → MvPolynomial W E) (a b : V → MvPolynomial W E) (D : ℕ)
    (ha : ∀ v, (a v).totalDegree ≤ D) (hb : ∀ v, (b v).totalDegree ≤ D)
    (c : V → I → MvPolynomial W E) (hc : ∀ v i, (c v i).totalDegree ≤ D)
    (hdiff : ∀ v, ∑ i, c v i * F i = a v - b v) (p : MvPolynomial V E) :
    ∃ A : I → MvPolynomial W E, (∀ i, (A i).totalDegree ≤ D * p.totalDegree) ∧
      ∑ i, A i * F i = aeval a p - aeval b p := by
  classical
  let property (q : MvPolynomial V E) :=
    (aeval a q).totalDegree ≤ D * q.totalDegree ∧
    ∃ A : I → MvPolynomial W E, (∀ i, (A i).totalDegree ≤ D * q.totalDegree) ∧
      ∑ i, A i * F i = aeval a q - aeval b q
  have mono : ∀ s r, property (monomial s r) := by
    apply induction_on_monomial
    · intro r
      exact ⟨by simp, fun _ => 0, by simp, by simp⟩
    · intro q v hq
      by_cases hz : q = 0
      · subst q
        exact ⟨by simp, fun _ => 0, by simp, by simp⟩
      obtain ⟨hdeg, A, hA, hAsum⟩ := hq
      have htotal : (q * X v).totalDegree = q.totalDegree + 1 := by
        rw [totalDegree_mul_of_isDomain hz (X_ne_zero v), totalDegree_X]
      simp only [property, map_mul, aeval_X, htotal, Nat.mul_add, Nat.mul_one]
      refine ⟨(totalDegree_mul _ _).trans (Nat.add_le_add hdeg (ha v)), ?_⟩
      refine ⟨fun i => aeval a q * c v i + A i * b v, fun i => ?_, ?_⟩
      · exact (totalDegree_add ..).trans (max_le
          ((totalDegree_mul ..).trans (Nat.add_le_add hdeg (hc v i)))
          ((totalDegree_mul ..).trans (Nat.add_le_add (hA i) (hb v))))
      · simp only [add_mul, Finset.sum_add_distrib]
        calc
          _ = aeval a q * (∑ i, c v i * F i) + (∑ i, A i * F i) * b v := by
            rw [Finset.mul_sum, Finset.sum_mul]
            congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
          _ = _ := by rw [hdiff, hAsum]; ring
  choose A hA heq using fun s => (mono s (p.coeff s)).2
  refine ⟨fun i => ∑ s ∈ p.support, A s i, fun i => totalDegree_finsetSum_le fun s hs => ?_, ?_⟩
  · apply (hA s i).trans
    exact Nat.mul_le_mul_left _ ((totalDegree_monomial_le s _).trans (le_totalDegree hs))
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [heq, Finset.sum_sub_distrib, ← map_sum, ← p.as_sum]

private theorem separate_parameter {n : ℕ} (p : MvPolynomial (Fin n) E) :
    finSuccEquiv E n (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C x => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]

/-- Replacing the normalized coordinates by polynomials independent of the
parameter amounts to mapping the coefficients of the univariate relation. -/
private theorem specialize_parameter {n m : ℕ} (L : Fin m → MvPolynomial (Fin n) E)
    (U : MvPolynomial (Fin (m+1)) E) :
    finSuccEquiv E n (aeval (Fin.cons (X 0) (fun j => rename Fin.succ (L j))) U) =
      Polynomial.map (aeval L).toRingHom (finSuccEquiv E m U) := by
  induction U using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Polynomial.map_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ, separate_parameter]

/-- Extract the bounded certificate for an inconsistent system from a monic
relation on a linear Noether normalization of its graph. -/
theorem graph_monic_certificate {n m H D : ℕ} (F : I → MvPolynomial (Fin n) E)
    (hF : ∀ i, (F i).totalDegree ≤ D)
    (Q : Fin m → MvPolynomial (Fin (n+1)) E)
    (hQ : ∀ j, Q j ∈ Submodule.span E (Set.range (graphGenerator F)))
    (U : MvPolynomial (Fin (m+1)) E) (hU : U.totalDegree ≤ H)
    (hmonic : (finSuccEquiv E m U).Monic)
    (hzero : aeval (Fin.cons (X 0) Q) U = 0) :
    ∃ A : I → MvPolynomial (Fin n) E, (∀ i, (A i).totalDegree ≤ (D+1)*H) ∧
      ∑ i, A i * F i = 1 := by
  classical
  choose l c hl using fun j => graphGenerator_span_decompose F (hQ j)
  let L (j : Fin m) : MvPolynomial (Fin n) E := ∑ i, C (l j i) * X i
  have hlift (j) : rename Fin.succ (L j) = ∑ i, C (l j i) * X i.succ := by simp [L]
  let a : Fin (m+1) → MvPolynomial (Fin (n+1)) E := Fin.cons (X 0) (fun j => rename Fin.succ (L j))
  let b : Fin (m+1) → MvPolynomial (Fin (n+1)) E := Fin.cons (X 0) Q
  let diff : Fin (m+1) → I → MvPolynomial (Fin (n+1)) E :=
    Fin.cons (fun _ => 0) (fun j i => -(X 0 * C (c j i)))
  have ha (i) : (a i).totalDegree ≤ D+1 := by
    refine Fin.cases (by simp [a]) (fun j => ?_) i
    simp only [a, Fin.cons_succ, hlift]
    apply totalDegree_finsetSum_le
    intro u _
    simpa using (totalDegree_mul (C (l j u) : MvPolynomial (Fin (n+1)) E) (X u.succ)).trans
      (by simp)
  have hb (i) : (b i).totalDegree ≤ D+1 := by
    exact Fin.cases (by simp [b]) (fun j => graphGenerator_span_degree F hF (hQ j)) i
  have hdiff (i) : ∑ v, diff i v * rename Fin.succ (F v) = a i - b i := by
    refine Fin.cases (by simp [a,b,diff]) (fun j => ?_) i
    simp only [diff, a, b, Fin.cons_succ, hl, hlift, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.mul_sum]
    simp only [mul_assoc]
    abel
  have hd (i j) : (diff i j).totalDegree ≤ D+1 := by
    refine Fin.cases (by simp [diff]) (fun u => ?_) i
    simp only [diff, Fin.cons_succ, totalDegree_neg]
    exact (totalDegree_mul ..).trans (by simp)
  obtain ⟨M, hM, he⟩ := bounded_substitution_difference (fun i => rename Fin.succ (F i))
    a b (D+1) ha hb diff hd hdiff U
  have hz : aeval b U = 0 := hzero
  rw [hz, sub_zero] at he
  let d := (finSuccEquiv E m U).natDegree
  refine ⟨fun i => (finSuccEquiv E n (M i)).coeff d, fun i => ?_, ?_⟩
  · by_cases hc : (finSuccEquiv E n (M i)).coeff d = 0
    · simp [hc]
    · have := totalDegree_coeff_finSuccEquiv_add_le (M i) d hc
      change ((finSuccEquiv E n (M i)).coeff d).totalDegree ≤ _
      exact ((Nat.le_add_right _ d).trans this).trans ((hM i).trans (Nat.mul_le_mul_left _ hU))
  · have ht := congrArg (fun p => (finSuccEquiv E n p).coeff d) he
    change _ = (finSuccEquiv E n (aeval (Fin.cons (X 0) (fun j => rename Fin.succ (L j))) U)).coeff d at ht
    rw [specialize_parameter, Polynomial.coeff_map, hmonic.coeff_natDegree, map_one] at ht
    simpa only [map_sum, map_mul, separate_parameter, Polynomial.finsetSum_coeff,
      Polynomial.coeff_mul_C] using ht

end RadicalCertificate

end VPVNP
end Computability
end OAI
