import OAI.ThreeFlat.RAM.HistoryStageBoundedResources
import OAI.ThreeFlat.RAM.HistoryStageBatchResources
import OAI.ThreeFlat.RAM.HistoryPartyPairExec

namespace OAI
/-! # Static resources of bounded joins and party pairs -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

open private price_transport from OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources

private def pairPrice (checks payload boot gather : ℕ) := checks + payload + (11 + 4 * boot) + gather

private theorem pairPrice_eq (checks payload boot gather : ℕ) :
    checks + payload + (11 + 4 * boot) + gather = pairPrice checks payload boot gather := rfl

noncomputable def pairResources : ℕ :=
  pairPrice (batchResources true) (batchResources false) (HistoryPartyPair.formula pairBase).work (joinResources 2)

private theorem pairResources_eq :
    batchResources true + batchResources false + (11 + 4 * (HistoryPartyPair.formula pairBase).work) +
      joinResources 2 = pairResources := by
  unfold pairResources
  exact pairPrice_eq (batchResources true) (batchResources false) (HistoryPartyPair.formula pairBase).work (joinResources 2)

private theorem pair_program_bound {W : ℕ} (checks payload gather : Procedure W) (f : Formula 1)
    (addr c p boot g : ℕ) (ch : resources checks ≤ c) (pl : resources payload ≤ p)
    (gt : resources gather ≤ g) (work : f.work = boot) :
    resources (((checks.seq payload).seq (PhysicalInputPhases.writing (HeaderScan.closed f) Fin.elim0 addr 25)).seq gather)
      ≤ c + p + (11 + 4 * boot) + g := by
  rw [resources_seq, resources_seq, resources_seq, resources_write, HeaderScan.binds_closed, Nat.add_zero, work]
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add ch pl) _) gt

set_option maxRecDepth 12000 in
private theorem pair_formula_work (A : HistoryPartyBatch.Layout) :
    (HistoryPartyPair.formula A).work=(HistoryPartyPair.formula pairBase).work := by
  simp only [HistoryPartyPair.formula, HistoryPartyPair.pick, eqz, add, mul, Formula.work]

private theorem pair_program_cost {W : ℕ} (A : HistoryPartyBatch.Layout) :
    resources (HistoryPartyPair.procedure W A) ≤ batchResources true + batchResources false +
      (11 + 4 * (HistoryPartyPair.formula pairBase).work) + joinResources 2 := by
  unfold HistoryPartyPair.procedure
  exact pair_program_bound (HistoryPartyBatch.procedure W A true) (HistoryPartyBatch.procedure W A false)
    (HistoryBoundedBody.procedure W ⟨HistoryPartyPair.hub A, A.seed, A.commands⟩ 2)
    (HistoryPartyPair.formula A) (HistoryPartyPair.hub A) (batchResources true) (batchResources false)
    (HistoryPartyPair.formula pairBase).work (joinResources 2)
    (batch_resources (W := W) A true) (batch_resources (W := W) A false)
    (bounded_resources (W := W) ⟨HistoryPartyPair.hub A, A.seed, A.commands⟩ 2) (pair_formula_work A)

theorem pair_resources {W : ℕ} (A : HistoryPartyBatch.Layout) :
    resources (HistoryPartyPair.procedure W A) ≤ pairResources :=
  price_transport (resources (HistoryPartyPair.procedure W A))
    (batchResources true + batchResources false + (11 + 4 * (HistoryPartyPair.formula pairBase).work) + joinResources 2)
    pairResources (pair_program_cost (W := W) A) pairResources_eq


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
