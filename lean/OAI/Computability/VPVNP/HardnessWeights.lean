import OAI.Computability.VPVNP.HardnessCNF
import OAI.Computability.VPVNP.HardnessQuery

/-!
# Generating polynomials of satisfying assignments

Weights may live in any commutative semiring. When each weight is a variable or
a scalar, the literal CNF test realizes this polynomial by a projection of the
universal integer family. Its source index is polynomial when the number of
Boolean variables and the total number of literals are polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

open MvPolynomial
open scoped Classical

/-- Sum of assignment weights over the satisfying assignments of a CNF. -/
noncomputable def weightedCNF {R : Type*} [CommSemiring R] {k : ℕ}
    (φ : CNF k) (weight : Fin k → R) : R :=
  ∑ x, if Satisfies φ x then ∏ i, if x i then weight i else 1 else 0

theorem weightedCNF_eq_query {R τ : Type*} [CommRing R] {k : ℕ}
    (φ : CNF k) (weight : Projection R (Fin k) τ) :
    weightedCNF φ (fun i => (weight i).elim X C) =
      weightedPredicate (fun x => (query φ).eval x (literalCount φ) (query φ).start) weight := by
  unfold weightedPredicate weightedCNF
  apply Finset.sum_congr rfl
  intro x _
  simp only [query_eval_iff φ x le_rfl]

theorem weightedCNF_PProjects {F : Type*} [Field F] {τ : ℕ → Type} {k : ℕ → ℕ}
    (φ : ∀ n, CNF (k n)) (weights : ∀ n, Projection F (Fin (k n)) (τ n))
    (hk : PolynomiallyBounded k) (hsize : PolynomiallyBounded fun n => literalCount (φ n)) :
    PProjects (fun n => weightedCNF (φ n) (fun i => (weights n i).elim X C))
      (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) := by
  simp_rw [weightedCNF_eq_query]
  apply weightedQuery_PProjects (hk := hk) (hf := hsize)
  simpa only [card_state] using (PolynomiallyBounded.const 2).add hsize

end HardnessCNF

end VPVNP
end Computability
end OAI
