import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentInitialRegisterArchive
import OAI.Hierarchy.DescentSeedRegisterLayout

namespace OAI
/-! Initial register page addresses, pitches and chart sizes. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentInitialHost DescentCompiler DescentDatedSeedStartup DescentColonies
noncomputable section
namespace DatePorts
def initial {F : Type} [Field F] {cp p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F cp p) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups payload Z : ℕ) : DatePorts:=
  ⟨PriorResetArchive.initial G op X R l k H groups payload Z,
    ⟨k,H,groups,3,256,l.fieldBits,l.packedLanes,l.packedLanes,l.packedLanes,l.packedLanes⟩,
    DescentDatedSeedStartup.operands X l k H groups,l.operandBits,l.operandLanes,3*l.groupsPerNode,1,
    DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k,H,DescentPrimitivePalette.printedBits G l.seedWidth Z op⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
