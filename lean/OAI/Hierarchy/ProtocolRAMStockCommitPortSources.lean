import OAI.Hierarchy.ProtocolRAMOccurrenceHeader
import OAI.Hierarchy.ProtocolRAMStockCommitDebit
import OAI.Hierarchy.ProtocolRAMRepairHistogram

namespace OAI
/-! # Histogram source addresses for the native stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {q d : ℕ}

/-- Bind the actual owner/port histogram lookup to the fixed catalog of a phase. -/
def Sources.ofBatch (old reserve half price owner parity : Bank) (mode slot ball port : Expr)
    (b : Batch q d) (tabs : Fin d → Fin q → Expr) : Sources :=
  let p := RepairHistogram.fromBatch owner parity (.lit 0) ball port b tabs
  ⟨old,reserve,half,price,mode,owner,parity,slot,p.credit,p.charge⟩

def PortHeader.area (h : PortHeader) (start goods limit : ℕ) : Area := ⟨start,h.rows,h.count,goods,limit⟩

def PortHeader.sources (h : PortHeader) (old reserve half price : Bank) (mode slot : Expr)
    (b : Batch q h.ports) (tabs : Fin h.ports → Fin q → Expr) :=
  Sources.ofBatch old reserve half price h.owner h.parity mode slot h.ballTerm h.fieldTerm b tabs

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
