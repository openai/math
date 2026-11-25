import OAI.Computability.NearSquareRoot.InterchangeROMStageTablePhysical
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyTemplate

/-! # Positive active width for each gate of a verified rectangle stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open InterchangeROMRepair InterchangeROMStageTable

theorem stage_active {j threshold : ℕ} {x : Data} (h : Valid j threshold x) (tag : Fin 5) :
    0 < (x.roleFrame.bank (inputBoundary tag)).length * Raw.rowCount x.m := by
  apply gate_source_positive
  · exact h.1.2.2.2.2.2.2.1
  · unfold Raw.rowCount Sizes.rows Sizes.basisCount Sizes.pencilOrder
    positivity

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
