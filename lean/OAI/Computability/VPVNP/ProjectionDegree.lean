import OAI.Computability.VPVNP.Circuits
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Total degree under variable-or-scalar projections -/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

/-- A p-projection preserves the total-degree upper bound, even when it identifies
variables or specializes them to arbitrary constants. -/
theorem Projection.totalDegree_hom_le {R σ τ : Type*} [CommSemiring R]
    (φ : Projection R σ τ) (p : MvPolynomial σ R) : (φ.hom p).totalDegree ≤ p.totalDegree := by
  classical
  rcases subsingleton_or_nontrivial R with h | h
  · rw [Subsingleton.elim (φ.hom p) 0, totalDegree_zero]
    exact Nat.zero_le _
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [Projection.hom, eval₂Hom_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd m.support _).trans (le_trans ?_ (le_totalDegree hm))
  apply Finset.sum_le_sum
  intro i hi
  cases hφ : φ i with
  | inl j => simp [hφ]
  | inr r =>
    simp only [hφ, Sum.elim_inr]
    change (C r ^ m i : MvPolynomial τ R).totalDegree ≤ m i
    rw [← map_pow, totalDegree_C]
    exact Nat.zero_le _

end VPVNP
end Computability
end OAI
