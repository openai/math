import OAI.Hierarchy.GraphClassification
import OAI.Hierarchy.GraphVNP
import OAI.Hierarchy.GridWitness

namespace OAI
/-! # Square grids witness the circuit separation under the graph lower bound -/

namespace Hierarchy

open Computability.VPVNP

/-- A Boolean assignment to the edges specifies a summand representation
over each field. A uniform degree-component border circuit bound would
force a uniform treewidth bound on the growing square grids. -/
theorem grid_witness_separation (F : Type*) [Field F] (lower : GraphBorderNecessity F) :
    IsVNP (contractionFamily F SquareGrid.graph) ∧
    ¬ IsVP (contractionFamily F SquareGrid.graph) ∧
    ¬ GraphFamily.PolynomialBorderCircuit SquareGrid.graph F := by
  have necessary : ¬ GraphFamily.PolynomialBorderCircuit SquareGrid.graph F :=
    fun h => SquareGrid.unbounded_treewidth (lower.circuit _ SquareGrid.polynomial_order h).1
  exact ⟨GraphFamily.contraction_isVNP _ F SquareGrid.polynomial_order SquareGrid.bounded_degree,
    fun h => necessary (GraphFamily.borderCircuit_of_isVP _ F h), necessary⟩

end Hierarchy

end OAI
