import OAI.Hierarchy.CircuitBalancedFactors
import OAI.Hierarchy.CircuitSlotFactors
import OAI.Hierarchy.ABPFirstCutRegroup
import OAI.Hierarchy.GraphWireCoefficients
import OAI.Hierarchy.GraphWireClass
import OAI.Hierarchy.SlotCoefficientClosure

namespace OAI
/-! # Balanced slot cuts for the degree-component border circuit model

The homogeneous decomposition of an exact circuit gives a matrix factorization
on each balanced cut. Selecting the squarefree coefficients is a polynomial
coordinate projection, so the degree-component border model gives membership
in the closure of sums of these bounded-rank matrices. In a graph contraction,
splitting the vertex slots identifies the resulting coefficients with the
independent equality wires on the edges.
-/

namespace Hierarchy.CircuitSlot

open ABPFirstCut Computability.BorderVNP MvPolynomial Computability.VPVNP
open scoped BigOperators Classical

variable {V : Type} {τ : V → Type} [Fintype V] [DecidableEq V] [∀ v, Fintype (τ v)]
  {F : Type*} [Field F]

/-- Each balanced vertex cut has one summand. The matrix rank bound is the
number of product generators in the homogeneous circuit decomposition. -/
theorem border_circuit_slot_sums {p : MvPolynomial (Σ i, τ i) F} {s : ℕ}
    (hd : 2 ≤ Fintype.card V)
    (small : DegreeBorderAtMost (fun t f => circuitSize f ≤ t) (Fintype.card V) s p) :
    (fun a => slotCoeff a Finset.univ (map (algebraMap F (AlgebraicClosure F)) p)) ∈
      imageClosure (rankSumsOn (fun U : balancedFamily V => U.val)
        (balancedCircuitTerms (Fintype.card V) s)) := by
  apply degreeModelClosure_slots (fun t f => circuitSize f ≤ t) _ _ small
  intro f hf
  obtain ⟨Q, P, degrees, expansion⟩ := circuit_balanced_factors hd hf
  exact (cutFactorization_of_products f Q P degrees expansion).exists_summands

end Hierarchy.CircuitSlot

namespace Hierarchy.IncidenceGraph

open ABPFirstCut Computability.BorderVNP CircuitSlot
open scoped BigOperators Classical

set_option maxHeartbeats 1000000 in
/-- The wire tensor of a graph with a border circuit of size `s` belongs to
the closure of sums with rank at most `(3*s+1)*(d+1)` on each balanced cut,
where `d` is the number of vertices. -/
theorem border_circuit_wire_cut_sums (G : IncidenceGraph) [DecidableEq G.V] [DecidableEq G.E]
    (F : Type*) [Field F] {q s : ℕ} (hd : 2 ≤ Fintype.card G.V)
    (small : DegreeBorderAtMost (fun t f => Computability.VPVNP.circuitSize f ≤ t)
      (Fintype.card G.V) s (G.contraction F q)) :
    (equalityWireRaw G.E (AlgebraicClosure F) q).coeff ∈
      imageClosure (rankSumsOn (fun U : balancedFamily G.V => legsOfCut G.portOwner U.val)
        (balancedCircuitTerms (Fintype.card G.V) s)) := by
  have h := closure_rankSumsOn_slotRead (F := AlgebraicClosure F)
    (τ := fun v : G.V => G.Incident v → Fin q) (ν := fun _ : G.E × Bool => Fin q)
    G.portOwner (G.portAssemble (q := q)) (fun U : balancedFamily G.V => U.val)
    (T := fun a => slotCoeff a Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (G.contraction F q)))
    (s := balancedCircuitTerms (Fintype.card G.V) s)
    (border_circuit_slot_sums (p := G.contraction F q) hd small)
  have heq : (fun a => slotCoeff a Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (G.contraction F q))) ∘
      slotRead G.portOwner (G.portAssemble (q := q)) =
      (equalityWireRaw G.E (AlgebraicClosure F) q).coeff := by
    funext x
    exact G.map_slotCoeff_portAssignment (algebraMap F (AlgebraicClosure F)) x
  exact heq ▸ h


end Hierarchy.IncidenceGraph

end OAI
