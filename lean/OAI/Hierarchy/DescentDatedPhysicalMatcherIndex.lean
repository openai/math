import OAI.Hierarchy.DescentDatedMatcherPageIndex
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentPrivateDepotPort
import OAI.Hierarchy.DescentHaloWalkRAM

namespace OAI
/-! The index used by the issued ordinary matcher's original donor page. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentHaloWalkRAM
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)

def matchAnchorIndex
    (i : Fin (breadth (v.ticket.depotShape v.short).degree*
      ((v.ticket.depotShape v.short).blocks*((v.ticket.depotShape v.short).cap*3)))) (f : Fin 5) :=
  DescentDatedOperandPages.matcherIndex (v.ticket.depotShape v.short) _ i f

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
