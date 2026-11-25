import OAI.Hierarchy.HereditaryWitnesses
import OAI.Hierarchy.CircuitBorderExtension
import OAI.Hierarchy.GridBalancedCuts
import OAI.Hierarchy.GridSeparation
import OAI.Computability.BorderVNP.ModelHomogenize

namespace OAI
/-! # Transfer fixed grid circuit lower bounds to the growing contraction family -/

namespace Hierarchy

open Computability.VPVNP MvPolynomial

abbrev circuitModel (K : Type*) [Field K] : SizeModel K := fun _ _ => HasCircuit

def circuitComponentSimulation (K : Type*) [Field K] :
    ComponentSimulation K (circuitModel K) where
  cost d s := 2*(d+1)^2*s
  polynomial _ _ hD hs := ((PolynomiallyBounded.const 2).mul
    ((hD.add (PolynomiallyBounded.const 1)).pow 2)).mul hs
  project d _ φ g h := (circuitSize_projection_le φ _).trans
    ((Computability.BorderVNP.circuitSize_homogeneousComponent_le d g).trans (Nat.mul_le_mul_left _ h))

def FixedGridCircuitHardness (K : Type*) [Field K] : Prop :=
  ∀ k : ℕ, ∃ h N, ∀ n ≥ N,
    ¬ GraphBorderAtMost (circuitModel (AlgebraicClosure K)) (SquareGrid.graph h) n (n^k)

theorem grids_eventually_not_borderCircuit_of_fixed (F : Type*) [Field F]
    (hard : FixedGridCircuitHardness (⊥ : Subfield F))
    (s : ℕ → ℕ) (hs : PolynomiallyBounded s) :
    ∃ N, ∀ n ≥ N,
      ¬ GraphBorderAtMost (circuitModel (AlgebraicClosure F)) (SquareGrid.graph n) n (s n) := by
  let K := (⊥ : Subfield F)
  obtain ⟨N, lower⟩ := eventually_hard_of_subgraphs (F := K) (circuitModel (AlgebraicClosure K))
    (circuitComponentSimulation _) (fun hst _ h => le_trans h hst)
    SquareGrid.graph SquareGrid.graph SquareGrid.polynomial_order
    (fun h => ⟨h, fun _ hn => ⟨SquareGrid.embed hn⟩⟩) hard s hs
  exact ⟨N, fun n hn small =>
    lower n hn (((SquareGrid.graph n).circuit_border_baseChange K F n (s n)).mp small)⟩

theorem grid_witness_of_fixed (F : Type*) [Field F]
    (hard : FixedGridCircuitHardness (⊥ : Subfield F)) :
    IsVNP (contractionFamily F SquareGrid.graph) ∧
    ¬ IsVP (contractionFamily F SquareGrid.graph) ∧
    ¬ GraphFamily.PolynomialBorderCircuit SquareGrid.graph F := by
  have necessary : ¬ GraphFamily.PolynomialBorderCircuit SquareGrid.graph F := by
    rintro ⟨s, bounded, small⟩
    obtain ⟨N, lower⟩ := grids_eventually_not_borderCircuit_of_fixed F hard s bounded
    exact lower N le_rfl (small N)
  exact ⟨GraphFamily.contraction_isVNP _ F SquareGrid.polynomial_order SquareGrid.bounded_degree,
    fun h => necessary (GraphFamily.borderCircuit_of_isVP _ _ h), necessary⟩

end Hierarchy

end OAI
