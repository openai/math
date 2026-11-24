import OAI.Computability.VPVNP.ChoiceWitness
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Paired variables for the universal counting polynomial

In equation (1.1) of *VP and VNP differ over every field*, the monomial for a word
`x` takes precisely one variable from each pair, with the second index recording its bit.
The coefficient and degree calculations hold for every coefficient function over a
commutative semiring.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- The exponent vector for the word `x` in the paired variables. -/
noncomputable def pairedExponent (x : Fin n → Bool) : (Fin n × Bool) →₀ ℕ :=
  ∑ j, Finsupp.single (j, x j) 1

@[simp] theorem pairedExponent_apply (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    pairedExponent x (i, b) = if x i = b then 1 else 0 := by
  classical
  rw [pairedExponent, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [Finsupp.single_apply]
  · intro j _ hji
    simp [hji]
  · simp

theorem pairedExponent_injective : Function.Injective (@pairedExponent n) := by
  intro x y h
  funext i
  have e := DFunLike.congr_fun h (i, y i)
  simpa [pairedExponent_apply] using e

/-- The polynomial in (1.1), with `u` providing its coefficients. -/
noncomputable def pairedPolynomial (u : (Fin n → Bool) → R) : MvPolynomial (Fin n × Bool) R :=
  ∑ x, C (u x) * ∏ j, X (j, x j)

theorem pairedPolynomial_eq_sum_monomial (u : (Fin n → Bool) → R) :
    pairedPolynomial u = ∑ x, monomial (pairedExponent x) (u x) := by
  simp only [pairedPolynomial, pairedExponent, monomial_sum_index, X]

/-- The coefficient of the monomial indexed by `x` recovers the value at `x`. -/
@[simp] theorem coeff_pairedPolynomial (u : (Fin n → Bool) → R) (x : Fin n → Bool) :
    (pairedPolynomial u).coeff (pairedExponent x) = u x := by
  classical
  simp [pairedPolynomial_eq_sum_monomial, coeff_monomial,
    pairedExponent_injective.eq_iff]

theorem pairedPolynomial_isHomogeneous (u : (Fin n → Bool) → R) :
    (pairedPolynomial u).IsHomogeneous n := by
  rw [pairedPolynomial_eq_sum_monomial]
  apply IsHomogeneous.sum
  intro x _
  apply isHomogeneous_monomial
  simp [pairedExponent, Finsupp.degree_single]

/-- Each individual variable has degree at most one, including in positive characteristic. -/
theorem pairedPolynomial_multilinear (u : (Fin n → Bool) → R) (z : Fin n × Bool) :
    (pairedPolynomial u).degreeOf z ≤ 1 := by
  classical
  rw [pairedPolynomial_eq_sum_monomial]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun x _ ↦ ?_)
  by_cases h : u x = 0
  · simp [h]
  · rcases z with ⟨i, b⟩
    rw [degreeOf_monomial_eq _ _ h, pairedExponent_apply]
    split <;> decide

theorem map_pairedPolynomial {S : Type*} [CommSemiring S] (f : R →+* S)
    (u : (Fin n → Bool) → R) :
    MvPolynomial.map f (pairedPolynomial u) = pairedPolynomial (f ∘ u) := by
  simp [pairedPolynomial]

theorem pairedPolynomial_totalDegree (u : (Fin n → Bool) → R) (x : Fin n → Bool)
    (hx : u x ≠ 0) : (pairedPolynomial u).totalDegree = n := by
  apply (pairedPolynomial_isHomogeneous u).totalDegree
  intro h
  apply hx
  rw [← coeff_pairedPolynomial u x, h]
  rfl

/-- Equation (1.1) over the integers, using the clocked table encoding from §1.1. -/
noncomputable def P (n : ℕ) : MvPolynomial (Fin n × Bool) ℤ :=
  pairedPolynomial (fun x ↦ (acceptingCount x : ℤ))

/-- Interpretation of the integer polynomial in a commutative ring. -/
theorem map_P {S : Type*} [CommRing S] (n : ℕ) :
    MvPolynomial.map (Int.castRingHom S) (P n) =
      pairedPolynomial (fun x ↦ (acceptingCount x : S)) := by
  rw [P, map_pairedPolynomial]
  simp [Function.comp_def]

/-- Expansion over input words and their canonical machine-choice strings. The verifier
in this identity is the deterministic Boolean function `verifiesInput`. -/
theorem map_P_eq_sum_witnesses {S : Type*} [CommRing S] (n : ℕ) :
    MvPolynomial.map (Int.castRingHom S) (P n) =
      ∑ x : Fin n → Bool, ∑ w : Fin (n ^ clockExponent) → Bool,
        (if verifiesInput x w then 1 else 0) *
          ∏ j, (X (j, x j) : MvPolynomial (Fin n × Bool) S) := by
  rw [map_P, pairedPolynomial]
  apply Finset.sum_congr rfl
  intro x _
  rw [acceptingCount_eq_sum_witnesses, map_sum, Finset.sum_mul]
  simp [apply_ite C]

@[simp] theorem coeff_P (x : Fin n → Bool) :
    (P n).coeff (pairedExponent x) = (acceptingCount x : ℤ) :=
  coeff_pairedPolynomial _ _

theorem P_isHomogeneous (n : ℕ) : (P n).IsHomogeneous n :=
  pairedPolynomial_isHomogeneous _

theorem P_multilinear (n : ℕ) (z : Fin n × Bool) : (P n).degreeOf z ≤ 1 :=
  pairedPolynomial_multilinear _ _

/-- The formal total degree remains exactly `n` after base change, including in positive
characteristic. For positive lengths, the all-zero input has exactly one accepting path. -/
theorem totalDegree_map_P {S : Type*} [CommRing S] [Nontrivial S] (n : ℕ) :
    (MvPolynomial.map (Int.castRingHom S) (P n)).totalDegree = n := by
  rw [map_P]
  by_cases hn : n = 0
  · subst n
    exact Nat.le_zero.mp (pairedPolynomial_isHomogeneous _).totalDegree_le
  · apply pairedPolynomial_totalDegree _ (fun _ ↦ false)
    simp [acceptingCount_allFalse (Nat.pos_of_ne_zero hn)]

theorem P_totalDegree (n : ℕ) : (P n).totalDegree = n := by
  by_cases hn : n = 0
  · subst n
    exact Nat.le_zero.mp (P_isHomogeneous 0).totalDegree_le
  · apply pairedPolynomial_totalDegree _ (fun _ ↦ false)
    simp [acceptingCount_allFalse (Nat.pos_of_ne_zero hn)]

end VPVNP
end Computability
end OAI
