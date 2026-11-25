import OAI.Hierarchy.ProtocolRAMTurnPrefix
import OAI.Hierarchy.ProtocolRAMRankGatherCost
import OAI.Hierarchy.ProtocolRAMTurnCost
import OAI.Hierarchy.TaggedWireOldOperands

namespace OAI
/-! # One charged native prefix for original weighted ranks, physical roles and all settled turn seats -/

namespace Hierarchy.ProtocolRAMTurnPaidCost
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM Calendar RouteSettlement ProbeStage CoreBoard HistoryRoles RoleProgram

theorem rank_clock (edges r src keys : ℕ) (b : RouteSettlement.Banks) (weights ids : Bank) :
    ProtocolRAMTurnPrefix.clock edges r src keys b weights ids=66+539*(edges+r)+6*edges := by
  simp only [ProtocolRAMTurnPrefix.clock,(ProtocolRAMTurnPrefix.term_work b edges).1,
    (ProtocolRAMTurnPrefix.term_work b edges).2,ProtocolRAMPackedCommon.clock,ProtocolRAMRankCost.gather,
    ProtocolRAMPackedCommon.inputBanks,Expr.work]
  ring

theorem rank_cheap (W edges r lo src keys counters dst : ℕ) (b : RouteSettlement.Banks) (weights ids : Bank) :
    CheapCode (ProtocolRAMTurnPrefix.program W edges r lo src keys counters dst b weights ids) :=
  cheap_seq (cheap_seq (scan_cheap _ _ _ _) (scan_cheap _ _ _ _))
    (cheap_seq (cheap_seq (ProtocolRAMRankCheap.gather _ _ _ _ _ _ _) (scan_cheap _ _ _ _))
      (TaggedShorterCommonScan.cheap _ _ _ _ _ _))

theorem clock_eq (board : Board) (stock : Inventory) (edges r src keys : ℕ) (b : RouteSettlement.Banks)
    (weights ids : Bank) (N sites seats : ℕ) :
    (ProtocolRAMTurnPrefix.clock edges r src keys b weights ids+board.extendedTime stock)+
      (72+6096*N+30*(sites*seats)) =
      board.extendedTime stock+138+539*(edges+r)+6*edges+6096*N+30*(sites*seats) := by
  rw [rank_clock]
  ring

end Hierarchy.ProtocolRAMTurnPaidCost

end OAI
