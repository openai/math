import OAI.Computability.BorderVNP.BranchSpecializationHeight
import OAI.Computability.VPVNP.LogBounds
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Counting coefficients in a finite incidence algebra

To choose the weighted slices in §9.2, record one remainder exponent below
`r` for each of `h` roots. Each of these slots is a polynomial in the `h`
graph parameters. Monomials in the `h` roots and one graph coordinate form
a strictly larger vector space at the degree used below.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open MvPolynomial BranchSpecialization

/-- Side radius of the box of source monomials in the dimension argument. -/
def radius (h r d : ℕ) := (max r 1 * ((h+1)*d+1))^h

/-- The extra source coordinate forces a strict dimension deficit even after
counting all `r^h` incidence slots. -/
theorem card_slots_lt (h r d : ℕ) :
    Fintype.card ((Fin h → Fin r) × BoundedMonomial (Fin h) ((h+1)*radius h r d*d)) <
      Fintype.card (Fin (h+1) → Fin (radius h r d+1)) := by
  let k := radius h r d
  have hcard : Fintype.card (BoundedMonomial (Fin h) ((h+1)*k*d)) ≤ ((h+1)*k*d+1)^h := by
    simpa using card_boundedMonomial_le (Fin h) ((h+1)*k*d)
  have hr : r ≤ max r 1 := le_max_left ..
  have hterm : (h+1)*k*d+1 ≤ ((h+1)*d+1)*(k+1) := by nlinarith
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  change r^h * Fintype.card (BoundedMonomial (Fin h) ((h+1)*k*d)) < (k+1)^(h+1)
  calc
    _ ≤ (max r 1)^h * (((h+1)*d+1)*(k+1))^h :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hr _) (hcard.trans (Nat.pow_le_pow_left hterm _))
    _ = k * (k+1)^h := by rw [mul_pow, ← mul_assoc, ← mul_pow]; rfl
    _ < (k+1)^(h+1) := by rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

/-- A linear dependence for a table of polynomials, simultaneously in all
remainder slots. The weights are scalars in the ground field. -/
theorem exists_slot_relation {K : Type*} [Field K] (h r d : ℕ)
    (table : (Fin (h+1) → Fin (radius h r d+1)) →
      (Fin h → Fin r) → MvPolynomial (Fin h) K)
    (hdeg : ∀ i j, (table i j).totalDegree ≤ (h+1)*radius h r d*d) :
    ∃ c : (Fin (h+1) → Fin (radius h r d+1)) → K, (∃ i, c i ≠ 0) ∧
      ∀ j, ∑ i, c i • table i j = 0 := by
  classical
  let b := (h+1)*radius h r d*d
  let vector (i) (j : (Fin h → Fin r) × BoundedMonomial (Fin h) b) := (table i j.1).coeff j.2.val
  have hdep : ¬ LinearIndependent K vector := by
    intro hi
    exact (card_slots_lt h r d).not_ge (by simpa only [Module.finrank_pi] using hi.fintype_card_le_finrank)
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨c, ⟨i₀, hi₀⟩, ?_⟩
  intro j
  apply MvPolynomial.ext
  intro a
  by_cases ha : a.degree ≤ b
  · simpa [vector, coeff_sum, coeff_smul, Finset.sum_apply] using congrFun hc (j, ⟨a, ha⟩)
  · have hzero (i) : (table i j).coeff a = 0 := by
      by_contra hne
      exact ha ((le_totalDegree (mem_support_iff.mpr hne)).trans (hdeg i j))
    simp [hzero]

end Branch.Incidence

end BorderVNP
end Computability
end OAI
