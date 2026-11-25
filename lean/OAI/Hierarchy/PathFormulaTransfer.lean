import OAI.Hierarchy.HereditaryWitnesses
import OAI.Hierarchy.GraphClassification
import OAI.Hierarchy.GraphBaseChange
import OAI.Hierarchy.FormulaHomogeneous
import OAI.Hierarchy.FormulaProjection

namespace OAI
/-! # Transfer fixed path formula lower bounds to the growing path family -/

namespace Hierarchy

open Computability.VPVNP

abbrev formulaModel (K : Type*) [Field K] : SizeModel K := fun _ _ => HasFormula

noncomputable def formulaComponentSimulation (K : Type*) [Field K] [Infinite K] :
    ComponentSimulation K (formulaModel K) where
  cost _ s := (s + 2) * (2*s+3)
  polynomial _ _ _ hs := (hs.add (PolynomiallyBounded.const 2)).mul
    (((PolynomiallyBounded.const 2).mul hs).add (PolynomiallyBounded.const 3))
  project D _ φ _ h := HasFormula.project (HasFormula.homogeneousComponent h D) φ

/-- Fixed paths with arbitrarily large exponents suffice in the prime field.
The polynomials themselves specialize over every field of the same characteristic. -/
theorem paths_eventually_not_borderFormula_of_fixed (F : Type*) [Field F]
    (hard : ∀ k : ℕ, ∃ h N, ∀ n ≥ N,
      ¬ GraphBorderAtMost (formulaModel (AlgebraicClosure (⊥ : Subfield F)))
        (IncidenceGraph.path h) n (n ^ k))
    (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N, ¬ GraphBorderAtMost (formulaModel (AlgebraicClosure F)) (IncidenceGraph.path n) n (s n) := by
  let K := (⊥ : Subfield F)
  have order : PolynomiallyBounded (fun n => Fintype.card (IncidenceGraph.path n).V) := by
    simpa only [IncidenceGraph.path_order] using PolynomiallyBounded.id
  obtain ⟨N, lower⟩ := eventually_hard_of_subgraphs (F := K) (formulaModel (AlgebraicClosure K))
    (formulaComponentSimulation _) (fun hst _ ⟨g, hg, bound⟩ => ⟨g,hg,bound.trans hst⟩)
    IncidenceGraph.path IncidenceGraph.path order eventually_contains_path hard s hs
  exact ⟨N, fun n hn small =>
    lower n hn (((IncidenceGraph.path n).formula_border_baseChange K F n (s n)).mp small)⟩

end Hierarchy

end OAI
