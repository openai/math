import OAI.Hierarchy.GraphClassification
import OAI.Hierarchy.PathWitness
import OAI.Hierarchy.BinaryTreeCutwidth
import OAI.Hierarchy.BinaryTreeWitnessSize

namespace OAI
/-! # The path and complete binary tree witnesses from the graph classification -/

namespace Hierarchy

open Computability.VPVNP

def completeBinaryTrees : GraphFamily := fun n => BinaryTree.graph (Nat.log 2 n)

private theorem pathsPolynomialOrder : GraphFamily.PolynomialOrder IncidenceGraph.path := by
  refine ⟨1, 1, 0, fun n _ => ?_⟩
  simp

private theorem treesPolynomialOrder : completeBinaryTrees.PolynomialOrder :=
  BinaryTree.log_order_polynomial

theorem paths_not_borderFormula (F : Type*) [Field F] (lower : GraphBorderNecessity F) :
    ¬ GraphFamily.PolynomialBorderFormula IncidenceGraph.path F := fun h =>
  IncidenceGraph.path_component_unbounded (lower.formula _ pathsPolynomialOrder h).1

theorem trees_not_borderABP (F : Type*) [Field F] (lower : GraphBorderNecessity F) :
    ¬ completeBinaryTrees.PolynomialBorderABP F := by
  intro h
  obtain ⟨b, hb⟩ := lower.abp _ treesPolynomialOrder h
  obtain ⟨n, _, hn⟩ := BinaryTree.log_cutwidth_unbounded b 0
  exact hn (hb n)

/-- The two explicit witnesses separate the three exact classes, and the two
lower bounds hold for degree-component border approximation. -/
theorem graph_witness_separations (F : Type*) [Field F]
    (literature : LowDegreeGraphTheorem F) (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    (IsVBP (contractionFamily F IncidenceGraph.path) ∧
      ¬ IsVF (contractionFamily F IncidenceGraph.path) ∧
      ¬ GraphFamily.PolynomialBorderFormula IncidenceGraph.path F) ∧
    (IsVP (contractionFamily F completeBinaryTrees) ∧
      ¬ IsVBP (contractionFamily F completeBinaryTrees) ∧
      ¬ completeBinaryTrees.PolynomialBorderABP F) := by
  obtain ⟨upper, lower⟩ := literature flats
  have hPath := paths_not_borderFormula F lower
  have hTree := trees_not_borderABP F lower
  exact ⟨⟨upper.abp _ pathsPolynomialOrder ⟨1, IncidenceGraph.path_cutwidth⟩,
      fun h => hPath (GraphFamily.borderFormula_of_isVF _ _ h), hPath⟩,
    ⟨upper.circuit _ treesPolynomialOrder ⟨3, fun _ => BinaryTree.degree_le_three _⟩
       ⟨1, fun _ => BinaryTree.treewidth_one _⟩,
      fun h => hTree (GraphFamily.borderABP_of_isVBP _ _ h), hTree⟩⟩

end Hierarchy

end OAI
