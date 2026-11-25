import OAI.Hierarchy.GraphVNPArity
import OAI.Hierarchy.GraphVNPDegree
import OAI.Hierarchy.GraphVNPIdentity
import OAI.Hierarchy.GraphVNPSize
import OAI.Hierarchy.GraphFamilyBounds

namespace OAI
/-! # VNP membership of bounded-degree graph contractions over every field -/

namespace Hierarchy.GraphFamily

open Computability.VPVNP

/-- Summing the one-hot edge verifier over all Boolean witnesses gives the
vertex-table contraction. Polynomial graph order and a uniform bound on
incidence degree bound the arity, total degree and exact circuit size. -/
theorem contraction_isVNP (G : ℕ → IncidenceGraph) (F : Type*) [Field F]
    (order : PolynomiallyBounded (fun n => Fintype.card (G n).V))
    (degree : ∃ b, ∀ n (v : (G n).V), (G n).degree v ≤ b) :
    IsVNP (contractionFamily F G) := by
  classical
  obtain ⟨b, hb⟩ := degree
  have pf := contractionFamily_pFamily F G order ⟨b,hb⟩
  have witnesses : PolynomiallyBounded (fun n => Fintype.card ((G n).Witness n)) :=
    ((order.mul (PolynomiallyBounded.const b)).mul PolynomiallyBounded.id).of_le
      (fun n => (G n).card_witness_le n (hb n))
  refine ⟨pf,fun n => (G n).Witness n,fun _ => inferInstance,
    fun n => (G n).witnessPolynomial F n,witnesses,⟨⟨?_,?_⟩,?_⟩,
    ?_⟩
  · simpa only [Fintype.card_sum] using pf.1.add witnesses
  · apply (order.mul ((PolynomiallyBounded.const 1).add
      ((PolynomiallyBounded.const b).mul PolynomiallyBounded.id))).of_le
    intro n
    exact (G n).totalDegree_witnessPolynomial_le F n b (hb n)
  · exact witnessPolynomial_size_polynomial F G order ⟨b,hb⟩
  · intro n
    refine ((G n).contraction_eq_sum_witness F n).trans ?_
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    simp


end Hierarchy.GraphFamily

end OAI
