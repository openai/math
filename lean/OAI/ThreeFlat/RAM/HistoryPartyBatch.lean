import OAI.ThreeFlat.RAM.HistoryPartyBatchFields
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistorySelectedOps
import OAI.ThreeFlat.RAM.HistoryScratch
import OAI.ThreeFlat.RAM.HistoryDyadic
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Producing and executing both real batches of a selected histogram party -/

namespace ThreeFlat.RAM.HistoryPartyBatch

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryPartyHeader HistoryScratch
open scoped Fin.CommRing

def dyadic (W : ℕ) (A : Layout) : Procedure W :=
  ⟨13,5,1,HistoryDyadic.block W,fun _ => (A.seed : Word W)⟩

/-- One actual native body. The three commands per real child are manufactured
from the live dyadic header and are consumed in order. The last scan publishes
the four-word root at the assigned per-node, per-motif and per-party address. -/
noncomputable def procedure (W : ℕ) (A : Layout) (checks : Bool) : Procedure W :=
  let boot := PhysicalInputPhases.writing (HeaderScan.closed (seedFormula A checks)) Fin.elim0 A.seed 37
  let header := PhysicalInputPhases.writing (actualHeader W A checks) Fin.elim0 A.batch 26
  let commands := HeaderScan.procedure ((A.seed+28 : ℕ) : Word W) 0 1 (batchTerm W A true)
  let args := HeaderScan.procedure ((A.seed+28 : ℕ) : Word W) 2 3 (batchTerm W A false)
  let scan := HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
    (Fin.last 0) (fun _ => ((A.seed+33 : ℕ) : Word W))
  let result := HeaderScan.procedure ((A.seed+28 : ℕ): Word W) 6 7 (HeaderScan.closed (resultWord A))
  (((boot.seq (dyadic W A)).seq header).seq commands).seq (args.seq (scan.seq result))


end ThreeFlat.RAM.HistoryPartyBatch

end OAI
