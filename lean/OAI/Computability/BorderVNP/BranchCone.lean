import OAI.Computability.BorderVNP.BranchGraph
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Clearing a common denominator in a rational image

Adjoining one homogeneous coordinate turns a rational chart parametrization into a
polynomial parametrization of its affine cone. The equations used below involve only
one extra parameter, independently of the number of outputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- Homogenize an equation to its total degree in a new coordinate. -/
noncomputable def coneEquation {ι K : Type*} [Field K] (p : MvPolynomial ι K) :
    MvPolynomial (Option ι) K :=
  ∑ m ∈ p.support, X none ^ (p.totalDegree - m.sum (fun _ e => e)) *
    rename some (monomial m (p.coeff m))

/-- Homogenization recovers the equation on the affine chart over any extension field. -/
theorem eval_coneEquation {ι K L : Type*} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial ι K) (a : L) (b : ι → L) (ha : a ≠ 0) :
    eval₂ f (fun j : Option ι => j.elim a b) (coneEquation p) =
      a ^ p.totalDegree * eval₂ f (fun i => b i / a) p := by
  classical
  conv_rhs => rhs; rw [p.as_sum]
  simp only [coneEquation, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_X, eval₂_rename,
    eval₂_monomial, Function.comp_apply, Option.elim, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, Finsupp.sum, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hm' := le_totalDegree hm
  change ∑ i ∈ m.support, m i ≤ p.totalDegree at hm'
  rw [← Nat.sub_add_cancel hm', pow_add]
  field_simp
  rw [Nat.add_sub_cancel]
  ring

/-- Scaling every homogeneous coordinate scales the value by the power of the
total degree, including at scale zero. -/
theorem eval_coneEquation_scale {ι K L : Type*} [Field K] [CommRing L] (f : K →+* L)
    (p : MvPolynomial ι K) (t : L) (x : Option ι → L) :
    eval₂ f (fun j => t * x j) (coneEquation p) =
      t ^ p.totalDegree * eval₂ f x (coneEquation p) := by
  classical
  simp only [coneEquation, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_X, eval₂_rename,
    eval₂_monomial, Function.comp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hm' := le_totalDegree hm
  change ∑ i ∈ m.support, m i ≤ p.totalDegree at hm'
  have e := congrArg (t ^ ·) (Nat.sub_add_cancel hm')
  rw [pow_add] at e
  rw [← e]
  ring

/-- Substituting polynomials of degree at most one cannot increase total degree. -/
theorem totalDegree_affine_substitution {ι κ K : Type*} [Field K]
    (p : MvPolynomial ι K) (u : ι → MvPolynomial κ K) (hu : ∀ i, (u i).totalDegree ≤ 1) :
    (aeval u p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => arg 1; rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine (totalDegree_mul ..).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd ..).trans ?_
  refine (Finset.sum_le_sum (fun i (_ : i ∈ m.support) => (totalDegree_pow ..).trans
    ((Nat.mul_le_mul_left (m i) (hu i)).trans_eq (Nat.mul_one _)))).trans ?_
  exact le_totalDegree hm

/-- A polynomial map from the affine cone with parameters `(s,x)`, sending these
parameters to `(s b(x), s a₁(x), …)`. -/
noncomputable def coneTable {ι K : Type*} [Field K] {h : ℕ} (b : MvPolynomial (Fin h) K)
    (a : ι → MvPolynomial (Fin h) K) : Option ι → MvPolynomial (Fin (h+1)) K :=
  fun i => X 0 * rename Fin.succ (i.elim b a)

/-- The cone chart has only one more parameter and its coordinate degrees rise by at most one. -/
theorem coneTable_degree {ι K : Type*} [Field K] {h d : ℕ} (b : MvPolynomial (Fin h) K)
    (a : ι → MvPolynomial (Fin h) K) (hb : b.totalDegree ≤ d) (ha : ∀ i, (a i).totalDegree ≤ d)
    (i : Option ι) : (coneTable b a i).totalDegree ≤ d + 1 := by
  have hi : (i.elim b a).totalDegree ≤ d := by cases i <;> simp [*, Option.elim]
  exact (totalDegree_mul ..).trans (by
    rw [totalDegree_X]; have := (totalDegree_rename_le Fin.succ _).trans hi; omega)

/-- Substitution into the cone table followed by evaluation at `(s,x)` evaluates the
homogeneous output variables at their indicated values. -/
theorem eval_coneTable {ι K L : Type*} [Field K] [Field L] {h : ℕ} (f : K →+* L)
    (b : MvPolynomial (Fin h) K) (a : ι → MvPolynomial (Fin h) K)
    (p : MvPolynomial (Option ι) K) (s : L) (x : Fin h → L) :
    eval₂ f (Fin.cons s x) (aeval (coneTable b a) p) =
      eval₂ f (fun j => s * eval₂ f x (j.elim b a)) p := by
  have hom : (eval₂Hom f (Fin.cons s x)).comp (aeval (coneTable b a)).toRingHom =
      eval₂Hom f (fun j => s * eval₂ f x (j.elim b a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply]
    · intro j
      simp [RingHom.comp_apply, coneTable, eval₂_rename]
  exact RingHom.congr_fun hom p

end Branch

end BorderVNP
end Computability
end OAI
