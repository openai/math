import OAI.ThreeFlat.RAM.HistoryStageCombinatorResources
import OAI.ThreeFlat.RAM.HistorySelectedOps
import OAI.ThreeFlat.RAM.TraceRawLookup

namespace OAI
/-! # Resource bounds for virtual endpoint rows and ready tapes -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators
noncomputable section

attribute [local irreducible] TraceRawLookup.virtual HistorySelectedOps.rows HistorySelectedOps.tariff

/-- Fixed instruction bound for the raw-trace adapter, including every S57 public load. -/
def rawLeafBinds := 866*1000234

private theorem raw_rows_size {W k : ℕ} (R : TraceRawLookup.Layout) (t : Term W k 4)
    (budget : t.binds ≤ 1000234) :
    (HistorySelectedOps.rows (TraceRawLookup.virtual W R t) []).binds ≤
      HistorySelectedOps.tariff [] + 3 * rawLeafBinds := by
  have raw : (TraceRawLookup.virtual W R t).binds ≤ rawLeafBinds :=
    (TraceRawLookup.virtual_binds W R t).trans (Nat.mul_le_mul_left 866 budget)
  have priced := HistorySelectedOps.rows_size_add W (TraceRawLookup.virtual W R t) rawLeafBinds
    (raw.trans (Nat.le_add_left _ _)) []
  simpa only [HistorySelectedOps.geometryList, List.flatMap_nil] using priced

private theorem leaf_program_bound {W k : ℕ} (f : Formula 1) (origin budget : ℕ)
    (rows : Term W k 1) (base : Fin k) (pub : Fin k → Word W)
    (seed : 4 + 42 * (2 * f.work + 4) ≤ 400000) (row : rows.binds ≤ budget) :
    resources ((PhysicalInputPhases.writing (HeaderScan.closed f) Fin.elim0 origin 42).seq
      (HistoryReadyTape.execute rows base pub)) ≤ 40 + 400000 + 4 * budget + k := by
  rw [resources_seq, resources_write, resources_tape, HeaderScan.binds_closed]
  omega

private def readyPrice (cap : ℕ) := 30 + 4 * cap

private theorem readyPrice_eq (cap : ℕ) : 30 + 4 * cap = readyPrice cap := rfl

noncomputable def readyResources : ℕ := readyPrice (HistorySelectedOps.tariff [])

private theorem readyResources_eq : 30 + 4 * HistorySelectedOps.tariff [] = readyResources := by
  unfold readyResources
  exact readyPrice_eq (HistorySelectedOps.tariff [])

private theorem price_transport (used limit target : ℕ) (bound : used ≤ limit) (same : limit = target) :
    used ≤ target := bound.trans_eq same

private theorem ready_scalar (work bound : ℕ) (small : work ≤ bound) :
    29 + 4 * work + 1 ≤ 30 + 4 * bound := by omega

private theorem ready_tape_cost {W : ℕ} (rows : Term W 1 1) (bound : ℕ)
    (data : Fin 1 → Word W) (small : rows.binds ≤ bound) :
    resources (HistoryReadyTape.execute rows (Fin.last 0) data) ≤ 30 + 4 * bound :=
  (resources_tape rows (Fin.last 0) data).le.trans (ready_scalar rows.binds bound small)

private theorem ready_literal_work (W : ℕ) :
    (Term.literal (0 : Word W) : Term W 0 4).binds = 1 := rfl

private theorem ready_literal_bound (W : ℕ) :
    (Term.literal (0 : Word W) : Term W 0 4).binds ≤ 1000234 :=
  (ready_literal_work W).trans_le (by decide : 1 ≤ 1000234)

private theorem ready_rows_geometry {W : ℕ} (initial : Term W 0 4) (small : initial.binds ≤ 1000234) :
    (HistorySelectedOps.rows initial (HistorySelectedOps.geometryList W [])).binds ≤ HistorySelectedOps.tariff [] :=
  HistorySelectedOps.rows_size_of W initial small []

private theorem ready_rows_plain {W : ℕ} (initial : Term W 0 4) (small : initial.binds ≤ 1000234) :
    (HistorySelectedOps.rows initial []).binds ≤ HistorySelectedOps.tariff [] := by
  simpa only [HistorySelectedOps.geometryList, List.flatMap_nil] using ready_rows_geometry initial small

private theorem ready_empty_rows (W : ℕ) :
    (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) []).binds ≤ HistorySelectedOps.tariff [] :=
  @ready_rows_plain W (.literal (0 : Word W)) (ready_literal_bound W)

private theorem empty_tape_cost (W : ℕ) (data : Fin 1 → Word W) :
    resources (HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
      (Fin.last 0) data) ≤ 30 + 4 * HistorySelectedOps.tariff [] :=
  @ready_tape_cost W (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
    (HistorySelectedOps.tariff []) data (ready_empty_rows W)

theorem ready_resources {W : ℕ} (data : Fin 1→Word W) :
    resources (HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0:Word W) : Term W 0 4) [])
      (Fin.last 0) data)≤readyResources :=
  price_transport
    (resources (HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
      (Fin.last 0) data))
    (30 + 4 * HistorySelectedOps.tariff []) readyResources (empty_tape_cost W data) readyResources_eq


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
