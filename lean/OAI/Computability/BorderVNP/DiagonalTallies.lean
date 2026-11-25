import OAI.Computability.BorderVNP.Diagonal
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Private monomial tallies for the border diagonal

Every surviving assignment in Section 11 reads the bit at each unary power
slot and selects an entry at each fixed gadget occurrence. The subtotals
and the resulting residue-matrix argument can be reconstructed without
evaluating any parameter on the branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial
open scoped BigOperators Classical

variable {Param Team : Type*} [Fintype Team] [Fintype Param] {b : ℕ}

/-- Exponent contributed by the binary power slots of a single substituted
batch. A power slot with its input set to zero contributes zero. -/
noncomputable def batchExponent (bits : Param → Fin b → Bool) : Param →₀ ℕ :=
  ∑ p, Finsupp.single p (∑ j : Fin b, if bits p j then 2 ^ j.val else 0)

private theorem sum_powers_two (b : ℕ) : (∑ j : Fin b, 2 ^ j.val) + 1 = 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
    omega

/-- Even unconstrained unary choices in one batch contribute at most the
number of parameters times the largest binary value. -/
theorem batchExponent_degree_le (bits : Param → Fin b → Bool) :
    (batchExponent bits).degree ≤ Fintype.card Param * (2 ^ b - 1) := by
  classical
  rw [batchExponent, map_sum]
  simp only [Finsupp.degree_single]
  calc
    _ ≤ ∑ _p : Param, ∑ j : Fin b, 2 ^ j.val := by
      gcongr with p hp j hj
      split <;> simp
    _ = Fintype.card Param * (2 ^ b - 1) := by
      have hs := sum_powers_two b
      have e : (∑ j : Fin b, 2 ^ j.val) = 2 ^ b - 1 := by omega
      simp [e]

/-- The total degree bound `R h (2^b − 1)` for a fully assigned term,
including any Boolean assignment admitted after shortening. -/
theorem exponent_degree_le (bits : Team → Param → Fin b → Bool) :
    (∑ t, batchExponent (bits t)).degree ≤
      Fintype.card Team * Fintype.card Param * (2 ^ b - 1) := by
  rw [map_sum]
  calc
    _ ≤ ∑ _t : Team, Fintype.card Param * (2 ^ b - 1) :=
      Finset.sum_le_sum fun t _ => batchExponent_degree_le (bits t)
    _ = _ := by simp [mul_assoc]

/-- The product of the unary weights is the monomial specified by the team
tallies. This identity takes place in the formal parameter ring. -/
theorem unary_weights_eq_monomial {E : Type*} [CommSemiring E]
    (bits : Team → Param → Fin b → Bool) :
    (∏ t, ∏ p, ∏ j : Fin b,
      if bits t p j then (X p : MvPolynomial Param E) ^ (2 ^ j.val) else 1) =
      monomial (∑ t, batchExponent (bits t)) 1 := by
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [batchExponent, monomial_sum_one]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← X_pow_eq_monomial, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  split <;> simp_all

variable {Gadget E : Type*} [Fintype Gadget] [CommSemiring E]

/-- Reconstruct the product of gadget values from the per-team count arrays.
The expression uses the convention `a^0 = 1` also at a zero entry. -/
theorem gadget_weights_eq_tally (values : Gadget → E) (δ : Team → Gadget → ℕ) :
    (∏ t, ∏ g, values g ^ δ t g) = ∏ g, values g ^ (∑ t, δ t g) := by
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum]

/-- Every consistent assignment supplies exactly one broadcast of its
subtotals, including the binary use bit of every weighted unary slot. -/
theorem unique_tally_broadcast {Path Broadcast : Type*} [Fintype Path] [Fintype Broadcast]
    [DecidableEq Broadcast] (compute : Path → Broadcast) (weight : Path → Broadcast → E) :
    (∑ e, ∑ d, if compute e = d then weight e d else 0) =
      ∑ e, weight e (compute e) := by
  simp

end Diagonal

end BorderVNP
end Computability
end OAI
