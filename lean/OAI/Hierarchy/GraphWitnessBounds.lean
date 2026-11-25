import OAI.Hierarchy.FixedPathFormula
import OAI.Hierarchy.TreeABPSeparation
import OAI.Hierarchy.PathABP
import OAI.Hierarchy.BinaryTreeWitnessCircuit

namespace OAI
/-! # The explicit arithmetic witnesses on homogeneous spectral flats

The larger model computes each graph contraction exactly. Every polynomial
size budget in the smaller degree-component border model fails eventually.
-/

namespace Hierarchy

open Computability.VPVNP

theorem graph_witness_eventual_bounds (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F)))
    (s t : ℕ → ℕ) (hs : PolynomiallyBounded s) (ht : PolynomiallyBounded t) :
    ∃ N, ∀ n ≥ N,
      (¬ GraphBorderAtMost (formulaModel (AlgebraicClosure F)) (IncidenceGraph.path n) n (s n)) ∧
      (¬ GraphBorderAtMost (abpModel (AlgebraicClosure F)) (completeBinaryTrees n) n (t n)) := by
  obtain ⟨i, path⟩ := paths_eventually_not_borderFormula_of_flats F flats s hs
  obtain ⟨j, tree⟩ := trees_eventually_not_borderABP_of_flats F flats t ht
  exact ⟨max i j, fun n hn =>
    ⟨path n ((le_max_left ..).trans hn), tree n ((le_max_right ..).trans hn)⟩⟩

theorem graph_witness_bounds (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    (IsVBP (contractionFamily F IncidenceGraph.path) ∧
      ¬ IsVF (contractionFamily F IncidenceGraph.path) ∧
      ¬ GraphFamily.PolynomialBorderFormula IncidenceGraph.path F) ∧
    (IsVP (contractionFamily F completeBinaryTrees) ∧
      ¬ IsVBP (contractionFamily F completeBinaryTrees) ∧
      ¬ completeBinaryTrees.PolynomialBorderABP F) := by
  have pathLower := paths_not_borderFormula_of_flats F flats
  have treeLower := trees_not_borderABP_of_flats F flats
  exact ⟨⟨path_isVBP F, fun h => pathLower (GraphFamily.borderFormula_of_isVF _ _ h), pathLower⟩,
    ⟨BinaryTree.isVP F, fun h => treeLower (GraphFamily.borderABP_of_isVBP _ _ h), treeLower⟩⟩


end Hierarchy

end OAI
