import OAI.Hierarchy.DescentRoleScansNames
import OAI.Hierarchy.DescentOrdinaryMaterialScan

namespace OAI
/-! The literal text and native clock of all fifteen material columns. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Sheets
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
theorem priced (s : Shape) (u : Setup) (H G M w base : ℕ) (both : Bank) :
    let p:=phase s u H G M w base both
    let n:=count s
    let pitch:=RoleScans.pitch (bits s) H G M
    p.ticks+7*names p.program=
      (4+10*(n*pitch))+(4+n*(4+44*(H*chunks G M)))+7*(15*(n*pitch+1)+(15+n*(11+4*20))) :=by
  dsimp only [phase,RoleScans.ticks]
  rw [RoleScans.cpu_names]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Sheets

end OAI
