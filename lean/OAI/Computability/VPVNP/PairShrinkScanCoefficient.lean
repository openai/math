import OAI.Computability.VPVNP.PairShrinkVertexImage
import OAI.Computability.VPVNP.PairShrinkGatherClock
import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.PairSimulationMapHandlerClock
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-! # The fixed coefficient of the installed shrinking map scan -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open Compression Compression.ShrinkMotif CompressorRecords

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)

local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i

/-- The finite clock table yields one constant for all grid and party
choices, before incorporating the fixed resident gather rows. -/
noncomputable def matrixFactor : ℕ :=
  (F).clockFactor * ((MapNativeClock.uniform B.shrink).choose+1) * (fieldFactor B.shrink+1)

/-- One fixed coefficient for the scheduled stage covers all stored
resident rows, their operand copies and the repeated private matrices. -/
noncomputable def stageCoefficient : ℕ :=
  let Q := (G).clockConstant (fieldFactor B.shrink+1)
  let stageRows := MapResidentRows.capacity (S.degreeExponent i.castSucc)
  1+2*stageRows+stageRows*(27+2*Fintype.card B.shrink.grid.demands+Q+matrixFactor B ord i)+
    stageRows*(3+Q+(F).probeBound)

/-- Sum of the resident-map cost coefficients over the shrinking stages in one fixed block
schedule. -/
noncomputable def scanCoefficient : ℕ := ∑ i : Fin S.steps, stageCoefficient B ord i

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
