import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Homogeneous components of the circuit grammar

In the grammar of Section 8.1 the degree-one states are arbitrary linear forms, and a
multiplication gate of degree `d` convolves the component lists of its input gates.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-`d` component of a product uses precisely the degree splits `i + j = d`. -/
theorem homogeneousComponent_mul (d : ℕ) (p q : MvPolynomial σ R) :
    homogeneousComponent d (p * q) = ∑ ij ∈ Finset.antidiagonal d,
      homogeneousComponent ij.1 p * homogeneousComponent ij.2 q := by
  classical
  let A := homogeneousSubmodule σ R
  have component (p : MvPolynomial σ R) (i : ℕ) :
      (DirectSum.decompose A p i : MvPolynomial σ R) = homogeneousComponent i p :=
    decomposition.decompose'_apply p i
  simp_rw [← component]
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  apply Finset.sum_subset
  · intro ij hij
    exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hij).2
  · intro ij hsum hout
    have h : ij.1 ∉ (DirectSum.decompose A p).support ∨
        ij.2 ∉ (DirectSum.decompose A q).support := by
      by_contra! hin
      exact hout (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hin,
        Finset.mem_antidiagonal.mp hsum⟩)
    rcases h with h | h <;> simp [DFinsupp.notMem_support_iff.mp h]

/-- The linear component is the linear combination of the individual variables with
coefficients given by their degree-one monomials. -/
theorem homogeneousComponent_one_eq_sum [Fintype σ] (p : MvPolynomial σ R) :
    homogeneousComponent 1 p = ∑ x, C (p.coeff (Finsupp.single x 1)) * X x := by
  classical
  ext1 m
  rw [coeff_homogeneousComponent, coeff_sum]
  by_cases h : m.degree = 1
  · have hc : (Finsupp.toMultiset m).card = 1 := by rw [Finsupp.card_toMultiset]; exact h
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hc
    have hm : m = Finsupp.single x 1 := by
      simpa using congrArg Multiset.toFinsupp hx
    subst m
    simp [coeff_X, Finsupp.single_left_inj one_ne_zero]
  · have hx (x : σ) : Finsupp.single x 1 ≠ m := by
      rintro rfl
      exact h (Finsupp.degree_single _ _)
    simp [h, coeff_X, hx]

end VPVNP
end Computability
end OAI
