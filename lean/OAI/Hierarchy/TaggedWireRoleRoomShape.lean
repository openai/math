import OAI.Hierarchy.TaggedWireRoleChart
import OAI.Hierarchy.TaggedWireRoleIndices
import OAI.Hierarchy.TaggedWirePublicPorts
import OAI.Hierarchy.TaggedShorterStageDirectory

namespace OAI
/-! # Dimensions of the original role table for the selected physical directory -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe TaggedShorterSupergroups ReportSockets WireTelescope
open scoped Classical
variable {h W k attempts H R : ℕ} (S : PurchaseSampler)
namespace RoleRoom

variable (dir : Directory (reserved h W (copies k attempts)) H)
def shape (edges : ℕ) : Sizes :=
  ⟨Fintype.card (Old h W k edges),Fintype.card (Public S h W k attempts),R,
    2^h,(siteLast h (2^W) k+1)*(2*k),dir.groups,H⟩

end RoleRoom
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
