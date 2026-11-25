import OAI.Hierarchy.ProtocolRAMPackedRanked
import OAI.Hierarchy.ProtocolRAMRankGatherCost

namespace OAI
/-! # Cost and cheap opcodes for recomputing the installed supergroup counter bank -/

namespace Hierarchy.ProtocolRAMPackedRanked
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM

theorem clock_eq (L : Layout) (N bins : ℕ) (width packed bias classes weights : Bank) :
    clock L N bins width packed bias classes weights=81+391*N+6*bins := by
  simp only [clock,ProtocolRAMPackedInputs.spreadAddress,ProtocolRAMPackedInputs.triple,
    ProtocolRAMGeneratedWrite.work,ProtocolRAMPackedInputs.terms,ProbeStage.Native.columns,
    ProtocolRAMPackedCommon.clock,ProtocolRAMRankCost.gather,ProtocolRAMPackedCommon.inputBanks,
    ProtocolRAMPackedInputs.keyWord,ProtocolRAMPackedInputs.weight,ProtocolRAM.clock,Pass.clock,Expr.work]
  ring

theorem cheap (L : Layout) (W N bins : ℕ) (width packed bias classes weights : Bank) :
    CheapCode (program L W N bins width packed bias classes weights) := by
  apply cheap_seq (cheap_seq (ProtocolRAMRankCheap.generated _ _ _ _ _ _) (ProtocolRAM.program_cheap _ _))
  exact cheap_seq (cheap_seq (ProtocolRAMRankCheap.gather _ _ _ _ _ _ _) (scan_cheap _ _ _ _)) (TaggedShorterCommonScan.cheap _ _ _ _ _ _)


end Hierarchy.ProtocolRAMPackedRanked

end OAI
