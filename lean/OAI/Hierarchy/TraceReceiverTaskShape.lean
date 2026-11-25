import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.CountedProcedure

namespace OAI
/-! # Counting native labels, registers and public operands of the terminal scan instructions -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure

variable {W k : ℕ}

def size (P : Procedure W) := P.labels+P.registers+P.slots

theorem size_seq (P Q : Procedure W) : size (P.seq Q)=size P+size Q := by
  change P.labels+Q.labels+(P.registers+Q.registers)+(P.slots+Q.slots)=_
  unfold size
  omega

theorem size_counted (P : Procedure W) (cell : Word W) : size (P.counted cell)=10+size P := by
  change 7+P.labels+(3+P.registers)+P.slots=10+(P.labels+P.registers+P.slots)
  omega

theorem size_scan (current : Word W) (start length : ℕ) (e : Term W 0 1) :
    size (HeaderScan.procedure current start length e)=18+4*e.binds := by
  change 13+e.labels+(4+e.binds)+0=18+4*e.binds
  rw [Term.labels_eq]
  omega

theorem size_writing (e : Term W k 1) (data : Fin k→Word W) (lo n : ℕ) :
    size (PhysicalInputPhases.writing e data lo n)=11+k+4*e.binds := by
  change 6+e.labels+(4+e.binds)+k=11+k+4*e.binds
  rw [Term.labels_eq]
  omega

end Hierarchy.TraceReceiverTasks

end OAI
