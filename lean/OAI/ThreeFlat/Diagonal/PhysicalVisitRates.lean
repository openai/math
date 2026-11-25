import OAI.ThreeFlat.RAM.HistoryMotifRates
import OAI.ThreeFlat.RAM.HistoryStageTariff

namespace OAI
/-! # Native compiler clock and per-level visit rate of a physical block -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open RAM.HistoryStageBody
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- One clock coefficient for both procedures actually mounted by the selected
stage arm. This is independent of the age, fold length and requested saving. -/
noncomputable def stageClockRate := 1+Physical.leafRuntimeRate+Physical.blockKernelRate B+6*Physical.blockRootRate B+Physical.blockGuardFee B+Physical.blockPageRate B

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section
variable {F : Type} [Field F] [Fintype F]

/-- The cost reserved for one traversal row uses its true S43 charge. Each
selected tree can copy the assembled child streams once at every level. -/
def Block.nativeVisitRate (B : Block F) (height K : ℕ) :=
  B.stageClockRate*K*(4*height+4)

def Block.nativeVisitFee (B : Block F) (height K depth : ℕ) :=
  (depth+1)*B.nativeVisitRate height K

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
