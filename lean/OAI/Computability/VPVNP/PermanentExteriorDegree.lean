import OAI.Computability.VPVNP.PermanentGraph

/-!
# The exterior column coefficient of the exact-one graph

After the internal gadgets have supplied their exits, each clause contributes its
own column and each ring row contributes the column of its chosen direction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial
open scoped BigOperators Classical

/-- The squarefree exterior monomial occurs exactly when every variable ring has
a single common orientation. -/
theorem coeff_ring_clause_columns {k m c : ℕ} {R : Type*} [CommSemiring R]
    (a : RingRow k m → Bool) :
    ((∏ u : RingRow k m, (X (.inl (ringTarget u (a u))) : MvPolynomial (Exterior k m c) R)) *
      ∏ z : Fin c, (X (Sum.inr z) : MvPolynomial (Exterior k m c) R)).coeff
        (fullDegree (Exterior k m c)) =
      if ∀ v j, a (v, j) = a (v, 0) then 1 else 0 := by
  let f : Exterior k m c → Exterior k m c := Sum.map (fun u => ringTarget u (a u)) id
  erw [← Fintype.prod_sum_type (fun u => (X (f u) : MvPolynomial (Exterior k m c) R))]
  simp only [X, prod_monomials, Finset.prod_const_one, coeff_monomial,
    degrees_eq_full_iff, f, Sum.map_bijective, Function.bijective_id, and_true,
    ringTarget_bijective_iff]

end PermanentReduction

end VPVNP
end Computability
end OAI
