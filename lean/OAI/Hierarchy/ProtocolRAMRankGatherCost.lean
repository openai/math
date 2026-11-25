import OAI.Hierarchy.ProtocolRAMRankGather
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap

namespace OAI
/-! # Work and opcode certificates of the row-gather pass shared by both native rankers -/

namespace Hierarchy.ProtocolRAMRankCost
open ProtocolRAM

theorem gather (src keys n : ℕ) (banks : ProtocolRAMRankGather.Columns) :
    ProtocolRAMRankGather.work n src keys banks ProtocolRAMRankGather.fields =
      48+n*(190+10*banks.order.work) := by
  simp only [ProtocolRAMRankGather.work,ProtocolRAMRankGather.fields,ProtocolRAMGeneratedWrite.work,
    ProtocolRAMRankGather.addressExpr,ProtocolRAMRankGather.valueExpr,ProtocolRAMRankGather.four,
    ProtocolRAMRankGather.three,ProtocolRAMRankGather.twice,Expr.work]
  ring

end Hierarchy.ProtocolRAMRankCost

namespace Hierarchy.ProtocolRAMRankCheap
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM

theorem gather (w n scratch src groups : ℕ) (banks : ProtocolRAMRankGather.Columns)
    (fs : List ProtocolRAMRankGather.Field) :
    CheapCode (ProtocolRAMRankGather.program w n scratch src groups banks fs) := by
  induction fs with
  | nil => exact scan_cheap _ _ _ _
  | cons f fs ih => exact cheap_seq ih (generated _ _ _ _ _ _)

end Hierarchy.ProtocolRAMRankCheap

end OAI
