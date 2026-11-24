import OAI.Computability.VPVNP.GrammarSize
import OAI.Computability.VPVNP.ParseHistogram

/-!
# Bounds for the coefficients of the label equations

The coefficient of a label monomial in the integer query `Bₓ` counts ordered
parses with that exact histogram whose terminals match the input word. The number
of such trees bounds every coefficient uniformly over subsequent choices of scalars.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial ParseGrammar
open scoped Classical

variable {H : Type*} [Fintype H] {n m : ℕ}

/-- The integer label coefficient counts matching trees, once per ordered parse. -/
theorem coeff_labelQuery_eq_card (d : Fin n) (h : H) (x : Fin m → Bool)
    (e : GrammarLabel (Fin m × Bool) H n →₀ ℕ) :
    (labelQuery d h x).coeff e =
      ((Finset.univ.filter fun p : OrderedParse (Fin m × Bool) H d.val ↦
        (p.leaves : Multiset (Fin m × Bool)) = (List.ofFn (fun i ↦ (i, x i)) : Multiset _) ∧
          histogram d h p = e).card : ℤ) := by
  classical
  rw [labelQuery, pairedExponent,
    coeff_eval_query_multiset (universalGrammar (Fin m × Bool) H n) d h (fun i ↦ (i, x i)),
    coeff_sum, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [universalGrammar_weight_eq_histogram]
  split_ifs <;> simp_all [coeff_monomial]

/-- Every queried coefficient is nonnegative and at most the total count of ordered
parses. In particular its bit length is bounded independently of field constants. -/
theorem coeff_labelQuery_bounds (d : Fin n) (h : H) (x : Fin m → Bool)
    (e : GrammarLabel (Fin m × Bool) H n →₀ ℕ) :
    0 ≤ (labelQuery d h x).coeff e ∧
      (labelQuery d h x).coeff e ≤
        (4 ^ d.val * Fintype.card H ^ (2 * d.val) * Fintype.card (Fin m × Bool) ^ (d.val + 1) : ℕ) := by
  rw [coeff_labelQuery_eq_card]
  constructor
  · positivity
  · exact_mod_cast (Finset.card_filter_le _ _).trans
      (Finset.card_univ.le.trans (card_orderedParse_le (Fin m × Bool) H d.val))

end VPVNP
end Computability
end OAI
