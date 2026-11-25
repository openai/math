import OAI.Hierarchy.Inclusions
import OAI.Hierarchy.GraphWitnessSeparation
import OAI.Hierarchy.Homogenization
import OAI.Hierarchy.SquareExponent

namespace OAI
/-! # Strict inclusions and the square exponent from the geometric and literature results

The graph assumption is the degree-component border classification in Theorem 6.1
of *Low-degree VNP lower bounds*. The circuit separation supplies a VNP family
outside VP over the given field. The Euclidean flat hypothesis is the main geometric
theorem of *Arithmetic formulas, branching programs, and circuits separate over every field*.
-/

namespace Hierarchy

open MatrixMultiplication LinearAlgebra.SpectralBooks Filter

theorem strict_inclusions_of_literature (F : Type*) [Field F]
    (graph : LowDegreeGraphTheorem F)
    (flats : ∀ d : ℕ, 0 < d → HasSpectralFlat (AlgebraicClosure (⊥ : Subfield F)) d)
    (circuits : CircuitSeparation F) :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  obtain ⟨⟨abp, formula, _⟩, ⟨treeCircuit, treeABP, _⟩⟩ :=
    graph_witness_separations F graph (allHomogeneousFlats_of_flats flats)
  refine strict_inclusions_of_witnesses F ?_ ?_ circuits
  · exact ⟨PolynomialFamily.ofFamily (contractionFamily F IncidenceGraph.path), abp, formula⟩
  · exact ⟨PolynomialFamily.ofFamily (contractionFamily F completeBinaryTrees), treeCircuit, treeABP⟩

end Hierarchy

end OAI
