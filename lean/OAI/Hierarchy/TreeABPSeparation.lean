import OAI.Hierarchy.FixedGraphABP
import OAI.Hierarchy.HereditaryWitnesses
import OAI.Hierarchy.GraphWitnessSeparation
import OAI.Hierarchy.GraphBaseChange
import OAI.Hierarchy.ABPHomogeneousComponent
import OAI.Hierarchy.ProjectionModel

namespace OAI
/-! # The complete binary tree's ABP lower bound from homogeneous spectral flats -/

namespace Hierarchy

open Computability.VPVNP MvPolynomial

noncomputable def abpComponentSimulation (K : Type*) [Field K] [Infinite K] :
    ComponentSimulation K (abpModel K) where
  cost _ s := (s + 2)^2
  polynomial _ _ _ hs := (hs.add (PolynomiallyBounded.const 2)).pow 2
  project D _ φ _ h := HasABP.project (HasABP.homogeneousComponent h D) φ

/-- The only geometric hypothesis is a homogeneous flat in each positive
dimension over the algebraic closure of the prime field. -/
theorem trees_eventually_not_borderABP_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F)))
    (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N, ¬ GraphBorderAtMost (abpModel (AlgebraicClosure F)) (completeBinaryTrees n) n (s n) := by
  let K := (⊥ : Subfield F)
  have fixedHard := fixed_binaryTree_hard K flats
  obtain ⟨N, lower⟩ := eventually_hard_of_subgraphs (F := K) (abpModel (AlgebraicClosure K))
    (abpComponentSimulation _) (fun hst _ ⟨g, hg, bound⟩ => ⟨g,hg,bound.trans hst⟩)
    completeBinaryTrees BinaryTree.graph BinaryTree.log_order_polynomial
    eventually_contains_binaryTree fixedHard s hs
  exact ⟨N, fun n hn small =>
    lower n hn (((completeBinaryTrees n).abp_border_baseChange K F n (s n)).mp small)⟩

theorem trees_not_borderABP_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    ¬ completeBinaryTrees.PolynomialBorderABP F := by
  rintro ⟨s, bounds, small⟩
  obtain ⟨N, lower⟩ := trees_eventually_not_borderABP_of_flats F flats s bounds
  exact lower N le_rfl (small N)

theorem trees_not_isVBP_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    ¬ IsVBP (contractionFamily F completeBinaryTrees) := fun h =>
  trees_not_borderABP_of_flats F flats (GraphFamily.borderABP_of_isVBP _ _ h)

end Hierarchy

end OAI
