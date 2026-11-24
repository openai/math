import OAI.Computability.VPVNP.ShrinkProcedureHistory
import OAI.Computability.VPVNP.RefreshProcedureRecords
import OAI.Computability.VPVNP.CompressionBlockHistory
import OAI.Computability.VPVNP.CompressionPowerHistory

/-!
# Iterated compression with a fixed system of wire identities

Theorem 7.1 of *VP and VNP differ over every field*. The expansion here uses
the packed six-party substeps and the port refresh on the actual lifted
slots. Its finite templates, degree schedule, number of lane coordinates
per block, energy allowance, and per-vertex history bound are fixed before
choosing a network or the number of blocks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

namespace BlockSchedule.Templates

open MotifConversion

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- Execute the fixed shrinking degrees followed by the expander refresh. -/
noncomputable def procedure : Procedure R (S.degreeExponent 0) (S.degreeExponent 0)
    S.laneBits S.positionFactor
    (refreshMultiplier S.baseDegree (2 ^ S.expanderExponent) S.poincare *
      shrinkMultiplier ^ S.steps) :=
  S.assembleBlock (B.shrinkProcedure f hf) (B.refreshProcedure f hf)

/-- The additive energy error is the same in every ring realizing the templates. -/
theorem procedure_error_eq {R' : Type*} [CommRing R'] (f' : B.Entry → R') (hf' : B.IsSolution f') :
    (B.procedure f hf).error = (B.procedure f' hf').error :=
  S.assembleBlock_error_congr (B.shrinkProcedure f hf) (B.shrinkProcedure f' hf')
    (B.refreshProcedure f hf) (B.refreshProcedure f' hf')
    (fun i => (B.shrinkProcedure_error f hf i).trans (B.shrinkProcedure_error f' hf' i).symm)
    ((B.refreshProcedure_error f hf).trans (B.refreshProcedure_error f' hf').symm)

/-- Fixed coefficient of the initial position count in the shared-width bound. -/
noncomputable def widthAllowance : ℝ :=
  Real.sqrt (B.procedure B.exists_solution.choose B.exists_solution.choose_spec).potentialWeight

/-- Uniform bound on each substep's records at a single vertex. -/
noncomputable def recordLimit : ℕ :=
  max 1 (max (Finset.univ.sup fun i : Fin S.steps =>
    State.shrinkHistoryFactor B.shrink (S.degreeExponent i.castSucc) (S.degreeExponent i.succ))
      B.refreshRecordConstant)

/-- The paper's `C₂`, enlarged to at least two. -/
noncomputable def growthConstant : ℕ := max 2 (B.recordLimit ^ (S.steps + 1))

theorem growthConstant_ge_two : 2 ≤ B.growthConstant := le_max_left _ _

/-- Local records are those of the constructed wire identities at each chosen site. -/
noncomputable def recordBounds : (B.procedure f hf).RecordBounds B.recordLimit (S.steps + 1) :=
  (S.assembleBlockRecords _ _ (B.shrinkProcedureRecords f hf) (B.refreshProcedureRecords f hf)).mono
    (le_max_right 1 _) le_rfl

/-- `T` complete blocks on an input with any sufficient number of lane coordinates. -/
noncomputable def execute {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    StateExecution R (S.degreeExponent 0) (n - T * S.laneBits) X :=
  (B.procedure f hf).repeatWithLanes T n h X

/-- The complete history of actual records on every branch of `execute`. -/
noncomputable def records {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    (B.execute f hf T h X).Records :=
  Procedure.repeatRecords (B.recordBounds f hf) _ T n (Nat.add_sub_of_le h).symm X

/-- Every branch restores the base degree, satisfies the shared-width saving
(7.4), and keeps all intermediate fields, individual map-entry degrees and
recursive vertex expansions within the stated exponential-in-block bounds. -/
theorem branch_bounds {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T h X).Choices) :
    let E := B.execute f hf T h X
    let Y := E.finalState z
    let chain := E.termChain (B.records f hf T h X) z
    X.positions = S.positionFactor ^ T * Y.positions ∧
      (Y.totalWidth : ℝ) ≤ Real.sqrt Y.energy ∧
      Real.sqrt Y.energy ≤ (Real.sqrt X.energy + B.widthAllowance * X.positions) / (2 : ℝ)^T ∧
      (∀ v, chain.occurrences (fun _ => 1) v ≤ B.growthConstant ^ T) ∧
      chain.AllRecordsLe (B.growthConstant ^ T * (X.maxWireWidth + 1)) ∧
      Y.maxWireWidth ≤ B.growthConstant ^ T * (X.maxWireWidth + 1) := by
  have hc := (B.procedure f hf).repeatWithLanes_bounds S.positionFactor_gt_two S.quarter T n h X z
  obtain ⟨hpos, hwidth, henergy⟩ := hc
  have heq : Real.sqrt (B.procedure f hf).potentialWeight = B.widthAllowance := by
    unfold widthAllowance Procedure.potentialWeight
    rw [B.procedure_error_eq f hf B.exists_solution.choose B.exists_solution.choose_spec]
  rw [heq] at henergy
  exact ⟨hpos, hwidth, henergy, Procedure.repeatWithLanes_history_bounds (B.recordBounds f hf)
    (le_max_left 1 _) T n h X z⟩

/-- The exact identity behind the estimates holds against any original
vertex factors, including those carrying fixed external indices. -/
theorem execute_contract {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (F : NetworkKernel.Factors R X.network) :
    let H := (B.execute f hf T h X).history
    NetworkKernel.contract X.network F = ∑ p : H.Path, H.weight F p :=
  (B.execute f hf T h X).history.contract_eq_sum_paths F

end BlockSchedule.Templates

open SpectralGeometry

/-- Theorem 7.1. The degree schedule and integral templates are chosen once,
before specializing the coefficient ring or selecting the input. Their
quantitative conclusions for every term are `Templates.branch_bounds`, and
their exact contraction identity is `Templates.execute_contract`. -/
theorem exists_iterated_compression {k : Type*} [Field k] (h : HasWireExpanders k) :
    ∃ (S : BlockSchedule k) (B : S.Templates),
      0 < S.laneBits ∧ 2 ≤ B.growthConstant ∧
      (∃ κ : B.Entry → k, B.IsSolution κ) ∧
      ∀ (R : Type*) [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)
        (n T : ℕ) (hn : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n),
        let E := B.execute κ hκ T hn X
        (∀ z : E.Choices,
          let Y := E.finalState z
          let chain := E.termChain (B.records κ hκ T hn X) z
          X.positions = S.positionFactor ^ T * Y.positions ∧
            (Y.totalWidth : ℝ) ≤ Real.sqrt Y.energy ∧
            Real.sqrt Y.energy ≤ (Real.sqrt X.energy + B.widthAllowance * X.positions) / (2 : ℝ)^T ∧
            (∀ v, chain.occurrences (fun _ => 1) v ≤ B.growthConstant ^ T) ∧
            chain.AllRecordsLe (B.growthConstant ^ T * (X.maxWireWidth + 1)) ∧
            Y.maxWireWidth ≤ B.growthConstant ^ T * (X.maxWireWidth + 1)) ∧
        ∀ F : NetworkKernel.Factors R X.network,
          NetworkKernel.contract X.network F = ∑ p : E.history.Path, E.history.weight F p := by
  obtain ⟨S⟩ := exists_blockSchedule h
  obtain ⟨B⟩ := S.exists_templates
  exact ⟨S, B, S.laneBits_pos, B.growthConstant_ge_two, B.exists_solution,
    fun _ _ κ hκ _ T hn X => ⟨B.branch_bounds κ hκ T hn X, B.execute_contract κ hκ T hn X⟩⟩

/-- The small-circuit contradiction fixes both templates and a joint field
assignment before the simulation is instantiated at any particular length.
Every sufficient input length and block count can then use the same
`Templates.execute`, `Templates.branch_bounds` and `Templates.execute_contract`. -/
theorem fixed_templates_of_small_circuits (k : Type*) [Field k] {C : ℕ} (hC : 1 ≤ C)
    (hsmall : ∀ N, ∃ n ≥ N, circuitSize (MvPolynomial.map (Int.castRingHom k) (P n)) ≤ n ^ C) :
    ∃ (S : BlockSchedule k) (B : S.Templates), ∃ f : B.Entry → k, B.IsSolution f := by
  obtain ⟨S⟩ := exists_blockSchedule (wire_expanders_of_small_circuits k hC hsmall)
  obtain ⟨B⟩ := S.exists_templates
  exact ⟨S, B, B.exists_solution⟩

end Compression

end VPVNP
end Computability
end OAI
