import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # Native expressions for the supergroup and socket tables -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets.SiteROM
open ProtocolRAM
def offsets (base G : ℕ) : Bank := ⟨base,ProtocolRAMPurchaseSampler.bits G⟩
def sites (base G H : ℕ) : Bank := ⟨base+G,ProtocolRAMPurchaseSampler.bits (G*H)⟩
def footprint (G H : ℕ) := G+G*H

def siteExpr (base G H : ℕ) (group slot : Expr) : Expr :=
  .lookup (sites base G H) (.op .add (.lookup (offsets base G) group) slot)

end Hierarchy.ProbeStage.ReportSockets.SiteROM

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
open ProtocolRAM ReportSockets
def positiveKey (offBase groups : ℕ) (g s : Expr) : Expr :=
  .op .add (.lookup (SiteROM.offsets offBase groups) g) s

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
end

end OAI
