import OAI.Hierarchy.TaggedWideHistoryUnit
import OAI.Hierarchy.TaggedWideOriginalRoleShelf

namespace OAI
/-! The calibrated size of the word reserved for every adjacent site. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (width : ℕ)
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs

/-- An entire neighbor word fits even when all its incident positive roles
share the same other endpoint. -/
def wideNeighborDigits (unitCost : ℕ) := Nat.clog 2 (degree*(v.wideHistoryUnit unitCost)*width+1)
def wideNeighborCap (unitCost : ℕ) := 2^(v.wideNeighborDigits width unitCost)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
