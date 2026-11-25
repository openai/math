import OAI.Optimization.LinearProgramming.Geometry.CircuitFamily
import OAI.Optimization.LinearProgramming.Farkas.Subspace
import OAI.Optimization.LinearProgramming.PriceGame.StatesRestart

/-! From complementary circuit supports to the integer hidden costs of the price game. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule PriceGame

/-- At every coordinate exactly one side is active, for every pair of compression assignments. -/
theorem fullCircuitEnvelope_alternative {N r s : ℕ}
    (D : Matrix (Fin r) (Fin N) ℝ) (E : Matrix (Fin s) (Fin N) ℝ)
    (hD : LinearIndependent ℝ D.row) (hE : LinearIndependent ℝ E.row)
    (hcomp : span ℝ (Set.range E.row) = (span ℝ (Set.range D.row)).orthogonalBilin (dotProductBilin ℝ ℝ))
    (f : (Fin (r - 1) → Fin N) → Fin N → ℝ) (g : (Fin (s - 1) → Fin N) → Fin N → ℝ)
    (i : Fin N) :
    (0 < circuitEnvelope (fullCircuitFamily r D f) i) ↔
      ¬ (0 < circuitEnvelope (fullCircuitFamily s E g) i) := by
  rw [fullCircuitEnvelope_pos_iff D hD, fullCircuitEnvelope_pos_iff E hE, hcomp]
  exact Farkas.subspace_coordinate_alternative _ i

/-- The specification of a returned label relative to one full assignment of minor logs. -/
def ValidNearLabel {N : ℕ} (C : Finset (Fin N → ℝ)) (flag : Bool) (q : Query N) (b : Bool) : Prop :=
  0 < circuitEnvelope C q.index →
    (∀ j, 0 < circuitEnvelope C j →
      circuitCost C q.index + (if flag then (q.prices q.index : ℝ) else -(q.prices q.index : ℝ)) ≤
        circuitCost C j + (if flag then (q.prices j : ℝ) else -(q.prices j : ℝ)) + 2) → b = flag

/-- Use the common extremal-sign input model for the compressed circuit envelope. The
real costs are used in analysis, and the positive active domain is enumerated only there. -/
noncomputable def circuitInstance {N R : ℕ} (C : Finset (Fin N → ℝ)) (flag : Bool)
    (anchor : Fin N) (ha : 0 < circuitEnvelope C anchor)
    (bound : ∀ i, 0 < circuitEnvelope C i → circuitCost C i ∈ Set.Icc 0 (R : ℝ)) :
    States.Rounding.Instance N anchor :=
  States.Rounding.unitInstance flag (Finset.univ.filter fun i => 0 < circuitEnvelope C i)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩) (circuitCost C) R
    (fun i hi => (bound i (Finset.mem_filter.mp hi).2).1)
    (fun i hi => (bound i (Finset.mem_filter.mp hi).2).2)

@[simp] theorem circuitInstance_range {N R : ℕ} (C : Finset (Fin N → ℝ)) (flag : Bool)
    (anchor : Fin N) (ha : 0 < circuitEnvelope C anchor)
    (bound : ∀ i, 0 < circuitEnvelope C i → circuitCost C i ∈ Set.Icc 0 (R : ℝ))
    (hR : 1 ≤ R) : (circuitInstance C flag anchor ha bound).range = R :=
  States.Rounding.unitInstance_range _ _ _ _ _ hR _ _

/-- A near-minimum coordinate in the shared oracle contract meets exactly the source's
active-set and signed-price inequalities for this circuit envelope. -/
theorem validNearLabel_on_instance {N R : ℕ} (C : Finset (Fin N → ℝ)) (flag : Bool)
    (anchor : Fin N) (ha : 0 < circuitEnvelope C anchor)
    (bound : ∀ i, 0 < circuitEnvelope C i → circuitCost C i ∈ Set.Icc 0 (R : ℝ))
    (q : Query N) {b : Bool} (hv : ValidNearLabel C flag q b)
    (hn : States.Restart.nearTwo (circuitInstance C flag anchor ha bound) q) : b = flag :=
  hv (Finset.mem_filter.mp hn.1).2 (fun j hj => hn.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))

end Geometry
end LinearProgramming
end Optimization
end OAI
