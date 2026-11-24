import OAI.Computability.VPVNP.ExactOneClauses
import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size of the exact-one verifier

A clause with `m` occurrences has `m` selector bits and `m²` filler bits.
The selector clause has `m` literals, and each of its `m²` pair clauses has at
most three literals. Summing over the original clauses gives quadratic bounds
in the total number of literal occurrences, even in the presence of empty clauses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

/-- Sum of the clause lengths in their indexed presentation. -/
theorem sum_lengths (φ : CNF k) : (∑ c : Fin φ.length, φ[c].length) = literalCount φ := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map φ List.length)

private theorem sum_squares_le (φ : CNF k) :
    (∑ c : Fin φ.length, φ[c].length ^ 2) ≤ literalCount φ ^ 2 := by
  calc
    _ ≤ ∑ c : Fin φ.length, φ[c].length * literalCount φ := by
      apply Finset.sum_le_sum
      intro c hc
      rw [pow_two, ← sum_lengths]
      exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun i _ => Nat.zero_le (φ[i].length)) hc)
    _ = _ := by rw [← Finset.sum_mul, sum_lengths, pow_two]

/-- The selectors and fillers use at most `L + L²` new variables. -/
theorem width_le (φ : CNF k) : width φ ≤ k + literalCount φ + literalCount φ ^ 2 := by
  simp only [width, Slot, Occ, PairOcc, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_prod, ← pow_two, sum_lengths, Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add_left (sum_squares_le φ) _) _

private theorem rows_length (φ : CNF k) (c : Fin φ.length) :
    (rows φ c).length = 1 + φ[c].length ^ 2 := by
  simp [rows, List.length_flatMap, pow_two, Nat.add_comm]

/-- One selector clause is retained per original clause, including empty ones. -/
theorem length_augment_le (φ : CNF k) : (augment φ).length ≤ φ.length + literalCount φ ^ 2 := by
  rw [augment, List.length_flatMap, ← Fin.sum_univ_def]
  simp only [rows_length, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  exact Nat.add_le_add_left (sum_squares_le φ) _

private theorem literalCount_flatMap {A : Type*} (xs : List A) (f : A → CNF k) :
    literalCount (xs.flatMap f) = (xs.map fun a => literalCount (f a)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [literalCount] using ih

private theorem pairClause_length_le (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    (pairClause φ c i j).length ≤ 3 := by
  by_cases h : j ≤ i <;> simp [pairClause, h]

private theorem literalCount_rows_le (φ : CNF k) (c : Fin φ.length) :
    literalCount (rows φ c) ≤ φ[c].length + 3 * φ[c].length ^ 2 := by
  change (selectorClause φ c).length + literalCount _ ≤ _
  simp only [selectorClause, List.length_map, List.length_finRange, literalCount_flatMap,
    ← Fin.sum_univ_def]
  apply Nat.add_le_add_left
  have h (i : Fin (φ[c].length)) : literalCount ((List.finRange _).map (pairClause φ c i)) ≤
      φ[c].length * 3 := by
    simp only [literalCount, List.map_map, ← Fin.sum_univ_def]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => pairClause_length_le φ c i j)
  simpa [pow_two, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

/-- A bound depending only on literal occurrences, even with arbitrarily many empty clauses. -/
theorem literalCount_augment_le (φ : CNF k) :
    literalCount (augment φ) ≤ literalCount φ + 3 * literalCount φ ^ 2 := by
  rw [augment, literalCount_flatMap, ← Fin.sum_univ_def]
  calc
    _ ≤ ∑ c : Fin φ.length, (φ[c].length + 3 * φ[c].length ^ 2) :=
      Finset.sum_le_sum (fun c _ => literalCount_rows_le φ c)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, sum_lengths, ← Finset.mul_sum]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (sum_squares_le φ)) _

/-- Polynomially bounded families of CNF verifiers retain polynomial width and literal count. -/
theorem polynomial_bounds {k : ℕ → ℕ} (φ : ∀ n, CNF (k n))
    (hk : PolynomiallyBounded k) (hL : PolynomiallyBounded fun n => literalCount (φ n)) :
    PolynomiallyBounded (fun n => width (φ n)) ∧
      PolynomiallyBounded (fun n => literalCount (augment (φ n))) :=
  ⟨((hk.add hL).add (hL.pow 2)).of_le (fun n => width_le (φ n)),
    (hL.add ((PolynomiallyBounded.const 3).mul (hL.pow 2))).of_le
      (fun n => literalCount_augment_le (φ n))⟩

end ExactOne

end VPVNP
end Computability
end OAI
