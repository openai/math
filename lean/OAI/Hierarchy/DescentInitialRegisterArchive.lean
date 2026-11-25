import OAI.Hierarchy.DescentSeedSharedCountBank
import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentInitialRolePages
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedNodeChart
import OAI.Hierarchy.DescentSeedPrintedPitch

namespace OAI
/-! # The seed's actual node, argument, role, and host count addresses -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler DescentInitialHost DescentSixParty DescentDatedSeedStartup
open DescentOperandStateBanks DescentSIMDLookup ProtocolRAM
noncomputable section
namespace PriorResetArchive
def initial {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (R : ℕ) (l : DescentDatedSeedStartup.Layout)
    (k H groups payload Z : ℕ) : PriorResetArchive:=
  let base:=DescentDatedSeedStartup.endAddress X l H groups k
  let arg:=Seed.Physical.bankStart X (DescentDatedSeedStartup.operandBase X l H groups) k groups l.operandLanes
  let next:=(DescentDatedSeedStartup.Input.nodeChart l k H groups).seedEnd base
  let lanes:=DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
  let hostCount:=DescentSeedInitialTable.sharedHostCountBank (DescentDatedSeedStartup.directoryBase X l H groups k) H groups l.packedLanes
  ⟨base,arg,true,PriorRolePages.initial X R l.seedWidth payload k H groups lanes next,hostCount⟩

end PriorResetArchive
end
end Hierarchy.DescentDatedAddressBook

end OAI
