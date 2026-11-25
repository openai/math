import OAI.Hierarchy.TaggedWireRoleRoomShape
import OAI.Hierarchy.TaggedWireTurnBoardNative
import OAI.Hierarchy.TaggedWireOriginalSocketExpr

namespace OAI
/-! # The fixed eleven-column terminal turn board -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets WireTelescope ProtocolRAM Calendar TaggedShorterSupergroups
variable {h W k H attempts R edges : ℕ} (S : PurchaseSampler)
    (dir : Directory (reserved h W (copies k attempts)) H)
local notation "z" => shape (R:=R) S dir edges
local notation "N" => Fintype.card (Old h W k edges)

def turnBoard (start out : ℕ) (core : CatalogueRows.CoreSource) (paid : Bool→Socket) : Board :=
  ⟨out,N,edges,(z).chart start,
    originalInputs ((z).chart start) start N ((z).ext start) ((z).axis start) h W k core paid,paid⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
