import OAI.Hierarchy.GraphWirePorts
import OAI.Hierarchy.ABPFirstCutCoeff

namespace OAI
/-! # The coefficients of graph contractions are equality wires -/

namespace Hierarchy.IncidenceGraph

open ABPFirstCut
open scoped Classical BigOperators

variable (G : IncidenceGraph)

/-- Splitting the physical legs of the contraction tensor gives one equality
wire per edge, for every finite loopless multigraph. -/
theorem slotCoeff_portAssignment (F : Type*) [Field F] {q : ℕ} (x : G.E × Bool → Fin q) :
    slotCoeff (G.portAssignment x) Finset.univ (G.contraction F q) =
      ∏ e : G.E, if x (e, false) = x (e, true) then (1 : F) else 0 := by
  rw [slotCoeff_graph_contraction]
  by_cases good : ∀ e : G.E, x (e, false) = x (e, true)
  · rw [ite_eq_left ((G.exists_labeling_iff_port_eq x).mpr good)]
    simp [good]
  · rw [ite_eq_right (fun h => good ((G.exists_labeling_iff_port_eq x).mp h))]
    obtain ⟨e, he⟩ := not_forall.mp good
    exact (Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right he)).symm

/-- The same equality wires appear after extending the coefficient field. -/
theorem map_slotCoeff_portAssignment {F K : Type*} [Field F] [Field K] (f : F →+* K) {q : ℕ}
    (x : G.E × Bool → Fin q) :
    slotCoeff (G.portAssignment x) Finset.univ (MvPolynomial.map f (G.contraction F q)) =
      ∏ e : G.E, if x (e, false) = x (e, true) then (1 : K) else 0 := by
  simpa [slotCoeff, MvPolynomial.coeff_map, apply_ite] using
    congrArg f (G.slotCoeff_portAssignment F x)

end Hierarchy.IncidenceGraph

end OAI
