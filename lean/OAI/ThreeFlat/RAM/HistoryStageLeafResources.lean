import OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources
import OAI.ThreeFlat.RAM.HistoryInitialBody

namespace OAI
/-! # Static resources of the initial seed and ready tape -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators
noncomputable section

open private raw_rows_size leaf_program_bound price_transport from OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources

attribute [local irreducible] TraceRawLookup.virtual TraceEndpointROM.fixed TraceEndpointROM.params
  HistorySelectedOps.rows HistorySelectedOps.tariff

theorem initial_rows_size {W : ℕ} (A : HistoryInitialSeed.Layout) :
    (HistoryInitialSeed.rows W A).binds ≤ HistorySelectedOps.tariff []+3*rawLeafBinds :=
  raw_rows_size A.rawLayout (TraceEndpointROM.fixed W) (TraceEndpointROM.fixed_binds W)


private def leafPrice (budget params : ℕ) := 40 + 400000 + 4 * budget + params

private theorem leafPrice_eq (budget params : ℕ) :
    40 + 400000 + 4 * budget + params = leafPrice budget params := rfl

noncomputable def leafResources : ℕ :=
  leafPrice (HistorySelectedOps.tariff [] + 3 * rawLeafBinds) (TraceEndpointROM.params + 1)

private theorem leafResources_eq :
    40 + 400000 + 4 * (HistorySelectedOps.tariff [] + 3 * rawLeafBinds) + (TraceEndpointROM.params + 1) =
      leafResources := by
  unfold leafResources
  exact leafPrice_eq (HistorySelectedOps.tariff [] + 3 * rawLeafBinds) (TraceEndpointROM.params + 1)

private theorem initial_program_cost {W : ℕ} (A : HistoryInitialSeed.Layout)
    (pub : Fin TraceEndpointROM.params → Word W) :
    resources (HistoryInitialSeed.procedure W A pub) ≤
      40 + 400000 + 4 * (HistorySelectedOps.tariff [] + 3 * rawLeafBinds) + (TraceEndpointROM.params + 1) := by
  unfold HistoryInitialSeed.procedure
  exact leaf_program_bound (HistoryInitialSeed.formula A) A.ctrl (HistorySelectedOps.tariff [] + 3 * rawLeafBinds)
    (HistoryInitialSeed.rows W A) (Fin.last TraceEndpointROM.params) (HistoryInitialSeed.nativeData A pub)
    (HistoryInitialSeed.seed_budget A) (initial_rows_size A)

theorem leaf_resources {W : ℕ} (A : HistoryInitialSeed.Layout) (pub : Fin TraceEndpointROM.params→Word W) :
    resources (HistoryInitialSeed.procedure W A pub)≤leafResources :=
  price_transport (resources (HistoryInitialSeed.procedure W A pub))
    (40 + 400000 + 4 * (HistorySelectedOps.tariff [] + 3 * rawLeafBinds) + (TraceEndpointROM.params + 1))
    leafResources (initial_program_cost A pub) leafResources_eq


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
