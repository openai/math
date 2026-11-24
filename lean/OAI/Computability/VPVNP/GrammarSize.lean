import OAI.Computability.VPVNP.GrammarLabels
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Size bounds for the ordered circuit grammar

A tree at layer `d` has `d` binary productions and `d + 1` terminals. There
are Catalan many ordered shapes, two state choices at each binary production,
and one variable choice at each terminal. The labels are shared among all parses.
-/

namespace OAI
namespace Computability
namespace VPVNP

open ParseGrammar

variable (V H : Type*) [Fintype V] [Fintype H]

/-- Number of ordered parses with fixed root state. -/
theorem card_orderedParse (d : ℕ) : Fintype.card (OrderedParse V H d) =
    catalan d * Fintype.card H ^ (2 * d) * Fintype.card V ^ (d + 1) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simpa using Fintype.card_congr (OrderedParse.leafEquiv (V := V) (H := H))
    | succ d =>
      rw [Fintype.card_congr (OrderedParse.nodeEquiv (V := V) (H := H) d),
        Fintype.card_sigma, catalan_succ, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      have hsplit : b.val ≤ d := Nat.le_of_lt_succ b.isLt
      simp only [Fintype.card_prod, ih b.val b.isLt, ih (d - b.val) (by omega)]
      have hs : 2 * (d + 1) = 2 * b.val + 2 * (d - b.val) + 1 + 1 := by omega
      have hv : d + 1 + 1 = (b.val + 1) + (d - b.val + 1) := by omega
      simp only [hs, hv, pow_add, pow_one]
      ring

/-- The shape count at layer `d` is at most `4 ^ d`. -/
theorem catalan_le_four_pow (d : ℕ) : catalan d ≤ 4 ^ d := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow d)

/-- A bound on the number of parses prior to imposing a coefficient query. -/
theorem card_orderedParse_le (d : ℕ) : Fintype.card (OrderedParse V H d) ≤
    4 ^ d * Fintype.card H ^ (2 * d) * Fintype.card V ^ (d + 1) := by
  rw [card_orderedParse]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (catalan_le_four_pow d))

/-- The grammar has polynomially many scalar labels in the variable count, the
state count and the degree cutoff. -/
theorem card_grammarLabel_le (n : ℕ) : Fintype.card (GrammarLabel V H n) ≤
    Fintype.card H * Fintype.card V + n ^ 2 * Fintype.card H ^ 3 := by
  rw [card_grammarLabel]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  calc
    (∑ d : Fin n, d.val) ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun d _ => d.isLt.le
    _ = n ^ 2 := by simp [pow_two]

end VPVNP
end Computability
end OAI
