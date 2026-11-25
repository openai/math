import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {σ ι : Type*}

/-- Sum of the absolute values of the integer coefficients. -/
def coeffMass (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ d ∈ p.support, (p.coeff d).natAbs

theorem natAbs_coeff_le (p : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    (p.coeff d).natAbs ≤ coeffMass p := by
  by_cases h : d ∈ p.support
  · exact Finset.single_le_sum (f := fun e => (p.coeff e).natAbs) (fun _ _ => Nat.zero_le _) h
  · simp [MvPolynomial.notMem_support_iff.mp h]

@[simp] theorem mass_zero : coeffMass (0 : MvPolynomial σ ℤ) = 0 := by
  simp [coeffMass, MvPolynomial.support_zero]

@[simp] theorem mass_monomial (m : σ →₀ ℕ) (a : ℤ) :
    coeffMass (MvPolynomial.monomial m a) = a.natAbs := by
  classical
  by_cases h : a = 0 <;> simp [coeffMass, MvPolynomial.support_monomial, h]

@[simp] theorem mass_X (i : σ) : coeffMass (MvPolynomial.X i : MvPolynomial σ ℤ) = 1 := by
  exact mass_monomial (Finsupp.single i 1) 1

@[simp] theorem mass_one : coeffMass (1 : MvPolynomial σ ℤ) = 1 := by
  exact mass_monomial 0 1

@[simp] theorem mass_neg (p : MvPolynomial σ ℤ) : coeffMass (-p) = coeffMass p := by
  simp [coeffMass, Int.natAbs_neg]

private theorem mass_eq_sum (p : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ))
    (h : p.support ⊆ s) : coeffMass p = ∑ d ∈ s, (p.coeff d).natAbs := by
  exact Finset.sum_subset h fun i _ hi => by simp [MvPolynomial.notMem_support_iff.mp hi]

theorem mass_add_le (p q : MvPolynomial σ ℤ) :
    coeffMass (p + q) ≤ coeffMass p + coeffMass q := by
  classical
  let s := p.support ∪ q.support
  rw [mass_eq_sum p s Finset.subset_union_left,
      mass_eq_sum q s Finset.subset_union_right,
      mass_eq_sum (p + q) s MvPolynomial.support_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using Int.natAbs_add_le (p.coeff i) (q.coeff i)

theorem mass_sum_le (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    coeffMass (∑ i ∈ s, p i) ≤ ∑ i ∈ s, coeffMass (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (mass_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mass_mul_le (p q : MvPolynomial σ ℤ) :
    coeffMass (p * q) ≤ coeffMass p * coeffMass q := by
  classical
  rw [MvPolynomial.mul_def]
  change coeffMass (∑ m ∈ p.support, ∑ n ∈ q.support,
    MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) ≤ _
  calc
    _ ≤ ∑ m ∈ p.support, coeffMass (∑ n ∈ q.support,
        MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) := mass_sum_le _ _
    _ ≤ ∑ m ∈ p.support, ∑ n ∈ q.support,
        coeffMass (MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) :=
      Finset.sum_le_sum fun _ _ => mass_sum_le _ _
    _ = _ := by
      simp only [mass_monomial, Int.natAbs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl

theorem mass_prod_le (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    coeffMass (∏ i ∈ s, p i) ≤ ∏ i ∈ s, coeffMass (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (mass_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

end Compression
end LinearProgramming
end Optimization
end OAI
