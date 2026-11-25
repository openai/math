import OAI.Hierarchy.TaggedWireOldBoardNative
import OAI.Hierarchy.TaggedWideSpillLayout
import OAI.Hierarchy.TaggedWideControlFields
import OAI.Hierarchy.ProtocolRAMDateSpillPage

namespace OAI
/-! # Additional date sheets for the signed-to-clipped intermediate and the two halves of a spill -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles RoleProgram
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open SiteControls
open scoped Classical Fin.CommRing BigOperators
variable {T : ℕ}

/-- The physical ranker writes the total clipped from each paid edge and
reads its original dated overflow by stock index. Each query goes through
the immutable original kind/index metadata. -/
def spillOnly (g : ProbeStage.CoreBoard.HistoryRoles.RoleProgram.Inventory) (page : DateSpill.Page) (paid : Bool) : Expr :=
  if paid then .branch .eq g.kind (.lit 0) (.lookup page.load g.index) (.lit 0)
  else .branch .eq g.kind (.lit 1) (.lookup page.overflow g.index) (.lit 0)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
