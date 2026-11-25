import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Native labels, registers and public words used by a procedure -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure DescriptorExpr

def resources {W : ℕ} (p : Procedure W) := p.labels+p.registers+p.slots

theorem resources_seq {W : ℕ} (p q : Procedure W) : resources (p.seq q)=resources p+resources q := by
  dsimp only [resources,PhysicalProcedure.Procedure.seq]
  omega

theorem resources_scan {W : ℕ} (t : Term W 0 1) (cur : Word W) (lo len : ℕ) :
    resources (HeaderScan.procedure cur lo len t)=18+4*t.binds := by
  dsimp only [resources,HeaderScan.procedure]
  rw [t.labels_eq];omega

end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
