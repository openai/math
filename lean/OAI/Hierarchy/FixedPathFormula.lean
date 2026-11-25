import OAI.Hierarchy.ConnectedFormulaForcing
import OAI.Hierarchy.FormulaWirePartitions
import OAI.Hierarchy.PathBlockGrowth
import OAI.Hierarchy.PathFormulaTransfer

namespace OAI
/-! # Fixed connected graphs and the formula lower bound on growing paths -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open FormulaPartitionRank
open scoped Classical BigOperators
noncomputable section

namespace IncidenceGraph

theorem connected_formula_force (F : Type*) [Field F] (G : IncidenceGraph) [Nonempty G.E]
    (P : HomogeneousFlat (AlgebraicClosure F) (Fintype.card G.E))
    (connected : ∀ u v, G.Connected u v) (hd : 2 ≤ Fintype.card G.V)
    {q s : ℕ} (hq : 2 ≤ q)
    (small : GraphBorderAtMost (formulaModel (AlgebraicClosure F)) G q s) :
    G.blockCount * Real.logb 2 q ≤
      (24 * Real.sqrt (2*Real.pi)) * Real.sqrt G.blockCount * Real.logb 2 ((s : ℝ)+2) +
        G.selectorError * Real.sqrt (Real.logb 2 q) :=
  G.connected_force_of_partition_closure (AlgebraicClosure F) P connected hd hq
    (G.border_formula_wire_partition_sums F hd small)


end IncidenceGraph

theorem fixed_path_hard (F : Type*) [Field F] (flats : AllHomogeneousFlats (AlgebraicClosure F)) :
    ∀ k : ℕ, ∃ d N, ∀ n ≥ N,
      ¬ GraphBorderAtMost (formulaModel (AlgebraicClosure F)) (IncidenceGraph.path d) n (n ^ k) := by
  intro k
  obtain ⟨d, _, hd, grows⟩ := PathForcing.block_superpolynomial
    (C := 24 * Real.sqrt (2*Real.pi)) (by positivity)
    (fun d => (IncidenceGraph.path d).selectorError) k 2
  obtain ⟨N, grow⟩ := Filter.eventually_atTop.mp grows
  let G := IncidenceGraph.path d
  have : Nonempty G.E := ⟨⟨0, by omega⟩⟩
  obtain ⟨P⟩ := flats (Fintype.card G.E) Fintype.card_pos
  refine ⟨d, max N 2, ?_⟩
  intro n hn small
  have force := G.connected_formula_force F P (IncidenceGraph.path_connected d)
    (by simpa [G] using hd) ((le_max_right ..).trans hn) small
  apply Nat.lt_irrefl (n ^ k)
  apply grow n ((le_max_left ..).trans hn) (n ^ k)
  simpa only [G, IncidenceGraph.blockCount, IncidenceGraph.path_order, PathForcing.blockCount,
    Nat.add_comm 1] using force

theorem paths_eventually_not_borderFormula_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F)))
    (s : ℕ → ℕ) (hs : Computability.VPVNP.PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N, ¬ GraphBorderAtMost (formulaModel (AlgebraicClosure F)) (IncidenceGraph.path n) n (s n) :=
  paths_eventually_not_borderFormula_of_fixed F (fixed_path_hard (⊥ : Subfield F) flats) s hs

theorem paths_not_borderFormula_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    ¬ GraphFamily.PolynomialBorderFormula IncidenceGraph.path F := by
  rintro ⟨s, bounds, small⟩
  obtain ⟨N, lower⟩ := paths_eventually_not_borderFormula_of_flats F flats s bounds
  exact lower N le_rfl (small N)

end
end Hierarchy

end OAI
