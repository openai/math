import OAI.Hierarchy.FixedCutFamilyForcing
import OAI.Hierarchy.GraphWireFirstCut
import OAI.Hierarchy.FixedWitnessTransfer
import OAI.Hierarchy.BinaryTreeCutwidth

namespace OAI
/-! # Fixed-graph branching-program lower bounds from orthogonal edge directions

The selector price is constant for a fixed graph and its fixed flat, even as
the edge alphabet grows. A growing cutwidth gives arbitrarily large
polynomial exponents without requiring any uniform bound on that constant.
-/

namespace Hierarchy

open scoped Classical

abbrev abpModel (K : Type*) [Field K] : SizeModel K :=
  fun σ finite => @HasABP K σ _ finite

namespace IncidenceGraph

theorem fixed_graph_border_abp (F : Type*) [Field F] (G : IncidenceGraph) [Nonempty G.E]
    (P : HomogeneousFlat (AlgebraicClosure F) (Fintype.card G.E))
    (b k : ℕ) (wide : ¬ G.CutwidthAtMost b)
    (slope : (k : ℝ) + 1 < Real.sqrt b) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s, GraphBorderAtMost (abpModel (AlgebraicClosure F)) G n s → n ^ k < s := by
  classical
  obtain ⟨N, growth⟩ := G.fixed_cut_family_hard (AlgebraicClosure F) P (G.cutFamily b) b k
    (fun U hU => (G.mem_cutFamily.mp hU).le) slope
  refine ⟨N, fun n hn s host => growth n hn s ?_⟩
  exact G.border_abp_wire_cut_sums F (G.cutFamily b) (G.empty_notMem_cutFamily b)
    (G.hitsEveryOrder_cutFamily wide) host

end IncidenceGraph

/-- Over the closure field supporting the flat, the fixed binary trees have
arbitrarily large eventual ABP border exponents as their height increases. -/
theorem fixed_binaryTree_hard (F : Type*) [Field F] (flats : AllHomogeneousFlats (AlgebraicClosure F)) :
    ∀ k : ℕ, ∃ h N, ∀ n ≥ N,
      ¬ GraphBorderAtMost (abpModel (AlgebraicClosure F)) (BinaryTree.graph h) n (n ^ k) := by
  intro k
  let b := (k+2)^2
  let h := 2*b+1
  let G := BinaryTree.graph h
  have : Nonempty G.E := ⟨BinaryTree.rootEdge (h := 2*b) false⟩
  obtain ⟨P⟩ := flats (Fintype.card G.E) Fintype.card_pos
  have slope : (k : ℝ) + 1 < Real.sqrt b := by
    dsimp [b]
    push_cast
    rw [Real.sqrt_sq (show 0 ≤ (k : ℝ) + 2 by positivity)]
    linarith
  obtain ⟨N, large⟩ := G.fixed_graph_border_abp F P b k
    (BinaryTree.not_cutwidth_odd b) slope
  exact ⟨h, N, fun n hn bound => (Nat.lt_irrefl _) (large n hn _ bound)⟩


end Hierarchy

end OAI
