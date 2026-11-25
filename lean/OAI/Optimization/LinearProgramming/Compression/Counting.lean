import OAI.Optimization.LinearProgramming.Compression.Determinants
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Counting the integer polynomials which can occur in a sum of subset products of minors. -/

open Finset

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The coefficients in the finite degree box determine an integer polynomial. -/
theorem card_le_of_bounded_integer_polynomials {ι σ : Type*} [Fintype σ]
    (S : Finset ι) (p : ι → MvPolynomial σ ℤ) (D C : ℕ)
    (hdeg : ∀ i ∈ S, (p i).totalDegree ≤ D)
    (hcoeff : ∀ i ∈ S, ∀ m, ((p i).coeff m).natAbs ≤ C)
    (hinj : Set.InjOn p S) : S.card ≤ (2 * C + 1) ^ ((D + 1) ^ Fintype.card σ) := by
  classical
  let exponent (a : σ → Fin (D + 1)) : σ →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun j => (a j : ℕ))
  let encode (i : S) (a : σ → Fin (D + 1)) : Fin (2 * C + 1) :=
    let z := (p i).coeff (exponent a)
    ⟨(z + (C : ℤ)).toNat, by
      have hz := hcoeff i i.property (exponent a)
      change z.natAbs ≤ C at hz
      omega⟩
  have hencode : Function.Injective encode := by
    intro i j h
    apply Subtype.ext
    apply hinj i.property j.property
    ext m
    by_cases hm : ∀ k, m k ≤ D
    · let a : σ → Fin (D + 1) := fun k => ⟨m k, Nat.lt_succ_of_le (hm k)⟩
      have hexp : exponent a = m := by ext k; simp [exponent, a]
      have hz := congrArg Fin.val (congrFun h a)
      change ((p i).coeff (exponent a) + (C : ℤ)).toNat =
        ((p j).coeff (exponent a) + (C : ℤ)).toNat at hz
      rw [hexp] at hz
      have hi := hcoeff i i.property m
      have hj := hcoeff j j.property m
      omega
    · have hzero (k : S) : (p k).coeff m = 0 := by
        by_contra hne
        apply hm
        intro l
        exact ((MvPolynomial.monomial_le_degreeOf l (MvPolynomial.mem_support_iff.mpr hne)).trans
          ((p k).degreeOf_le_totalDegree l)).trans (hdeg k k.property)
      rw [hzero i, hzero j]
  simpa using Fintype.card_le_of_injective encode hencode

/-- Count subsets of subset products after one evaluation distinguishes all their sums. -/
theorem subset_product_count {ι σ R : Type*} [Fintype σ] [CommRing R]
    (J : Finset ι) (P : ι → MvPolynomial σ ℤ) (eval : MvPolynomial σ ℤ →+* R) (D Q : ℕ)
    (hdeg : ∀ i ∈ J, (P i).totalDegree ≤ D)
    (hcoeff : ∀ A ⊆ J, ∀ m, ((∏ i ∈ A, P i).coeff m).natAbs ≤ Q)
    (hinj : Set.InjOn (fun U : Finset (Finset ι) => ∑ A ∈ U, ∏ i ∈ A, eval (P i))
      (↑J.powerset.powerset : Set (Finset (Finset ι)))) :
    2 ^ (2 ^ J.card) ≤ (2 ^ (J.card + 1) * Q + 1) ^ ((D * J.card + 1) ^ Fintype.card σ) := by
  classical
  let polys (U : Finset (Finset ι)) := ∑ A ∈ U, ∏ i ∈ A, P i
  have hdeg' (U : Finset (Finset ι)) (hU : U ∈ J.powerset.powerset) :
      (polys U).totalDegree ≤ D * J.card := by
    refine MvPolynomial.totalDegree_finsetSum_le fun A hA => ?_
    have hAJ := Finset.mem_powerset.mp (Finset.mem_powerset.mp hU hA)
    calc
      _ ≤ ∑ i ∈ A, (P i).totalDegree := MvPolynomial.totalDegree_finsetProd A P
      _ ≤ ∑ _i ∈ A, D := Finset.sum_le_sum fun i hi => hdeg i (hAJ hi)
      _ = D * A.card := by simp [Nat.mul_comm]
      _ ≤ D * J.card := Nat.mul_le_mul_left _ (Finset.card_le_card hAJ)
  have hcoeff' (U : Finset (Finset ι)) (hU : U ∈ J.powerset.powerset) (m : σ →₀ ℕ) :
      ((polys U).coeff m).natAbs ≤ 2 ^ J.card * Q := by
    have hcard : U.card ≤ 2 ^ J.card := by
      simpa using Finset.card_le_card (Finset.mem_powerset.mp hU)
    have hterm (A) (hA : A ∈ U) : |(∏ i ∈ A, P i).coeff m| ≤ (Q : ℤ) := by
      have h := hcoeff A (Finset.mem_powerset.mp (Finset.mem_powerset.mp hU hA)) m
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    have htotal : |(polys U).coeff m| ≤ (U.card : ℤ) * Q := by
      unfold polys
      rw [MvPolynomial.coeff_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa using Finset.sum_le_sum hterm
    have htotal' : ((polys U).coeff m).natAbs ≤ U.card * Q := by
      rw [← Int.natCast_natAbs] at htotal
      exact_mod_cast htotal
    exact htotal'.trans (Nat.mul_le_mul_right Q hcard)
  have hpoly : Set.InjOn polys (↑J.powerset.powerset : Set (Finset (Finset ι))) := by
    intro U hU V hV heq
    apply hinj hU hV
    simpa [polys] using congrArg eval heq
  have h := card_le_of_bounded_integer_polynomials J.powerset.powerset polys _ _ hdeg' hcoeff' hpoly
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Uniform degree and coefficient-mass bounds suffice for the subset-product count. -/
theorem subset_product_count_of_mass {ι σ R : Type*} [Fintype σ] [CommRing R]
    (J : Finset ι) (P : ι → MvPolynomial σ ℤ) (eval : MvPolynomial σ ℤ →+* R) (D M : ℕ)
    (hM : 0 < M) (hdeg : ∀ i ∈ J, (P i).totalDegree ≤ D)
    (hmass : ∀ i ∈ J, coeffMass (P i) ≤ M)
    (hinj : Set.InjOn (fun U : Finset (Finset ι) => ∑ A ∈ U, ∏ i ∈ A, eval (P i))
      (↑J.powerset.powerset : Set (Finset (Finset ι)))) :
    2 ^ (2 ^ J.card) ≤ (2 ^ (J.card + 1) * M ^ J.card + 1) ^
      ((D * J.card + 1) ^ Fintype.card σ) := by
  apply subset_product_count J P eval D (M ^ J.card) hdeg _ hinj
  intro A hAJ m
  calc
    _ ≤ coeffMass (∏ i ∈ A, P i) := natAbs_coeff_le _ _
    _ ≤ ∏ i ∈ A, coeffMass (P i) := mass_prod_le ..
    _ ≤ ∏ _i ∈ A, M := Finset.prod_le_prod fun i hi => hmass i (hAJ hi)
    _ = M ^ A.card := by simp
    _ ≤ M ^ J.card := Nat.pow_le_pow_right hM (Finset.card_le_card hAJ)

/-- The counting inequality of Lemma 3.1, specialized to the two input matrices. -/
theorem pairMinor_subset_product_count {R : Type*} [CommRing R] {rD rE N : ℕ}
    (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R)
    (hrows : rD + rE = N) (J : Finset (PairMinorIndex rD rE N))
    (hinj : Set.InjOn (fun U : Finset (Finset (PairMinorIndex rD rE N)) =>
      ∑ A ∈ U, ∏ i ∈ A, pairMinorValue D E i) J.powerset.powerset) :
    2 ^ (2 ^ J.card) ≤ (2 ^ (J.card + 1) * N.factorial ^ J.card + 1) ^
      ((N * J.card + 1) ^ (N ^ 2)) := by
  rw [← card_pairVariable hrows]
  apply subset_product_count_of_mass J pairMinorPolynomial
    (MvPolynomial.eval₂Hom (Int.castRingHom R) (pairValuation D E)) N N.factorial
    (Nat.factorial_pos N) (fun i _ => totalDegree_pairMinorPolynomial_le i)
    (fun i _ => coeffMass_pairMinorPolynomial_le i)
  simpa only [eval_pairMinorPolynomial] using hinj

end Compression
end LinearProgramming
end Optimization
end OAI
