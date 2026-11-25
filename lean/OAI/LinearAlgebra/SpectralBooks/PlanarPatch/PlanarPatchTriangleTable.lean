import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # The trivalent table of a polygon triangle -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators Classical
namespace PlanarPatch

variable {K : Type*} [CommSemiring K]

/-- A triangle receives one pair of vertex states across each of its three
sides. Its scalar weight is the check belonging to its root edge. -/
def triangleTable {A B C : Type*} (e : A → C → K) (p : A × C) (q : A × B) (r : B × C) : K :=
  if q.1 = p.1 ∧ r.2 = p.2 ∧ r.1 = q.2 then e p.1 p.2 else 0

/-- Summing the two child side indices leaves exactly the single sum over
the third corner, with multiplicity one. -/
theorem contract_triangleTable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A → C → K) (f : A → B → K) (g : B → C → K) (a : A) (c : C) :
    (∑ q : A × B, ∑ r : B × C, triangleTable e (a,c) q r * f q.1 q.2 * g r.1 r.2) =
      e a c * ∑ b : B, f a b * g b c := by
  simp only [Fintype.sum_prod_type, triangleTable]
  simp [ite_and, ite_mul, mul_assoc, Finset.mul_sum]

end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
