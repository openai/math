import OAI.Hierarchy.DescentResetTerminalRegisterLayout
import OAI.Hierarchy.DescentOrdinaryPeerCount
import OAI.Hierarchy.DescentPriorPrimitiveArchive
import OAI.Hierarchy.DescentInitialRegisterArchive
import OAI.Hierarchy.DescentOrdinaryArgumentsAfter
import OAI.Hierarchy.DescentResetRetainedPriorBanks

namespace OAI
/-! The previous date's node, argument, and primitive pages are registered together. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler DescentInitialHost DescentSixParty DescentSixParty.Chronology DescentDatedSeedStartup
open DescentOperandStateBanks DescentSIMDLookup ProtocolRAM
noncomputable section
namespace PriorResetArchive
def ordinary {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) : PriorResetArchive:=
  ⟨v.nodeBankBase floor,v.finalChart.out (v.metaEnd floor),false,PriorRolePages.ordinary v floor,
    DescentOrdinaryPeerCount.newCount (v.materialEnd floor) v.area.H v.area.D v.venue.hosts v.venue.degree⟩

def prior (p : PriorResetArchive) (v : DescentResetRetainedSetup.Layout) :=
  if p.seed then v.seedPrior p.nodeBase p.arguments else v.laterPrior p.nodeBase p.arguments
end PriorResetArchive
end
end Hierarchy.DescentDatedAddressBook

end OAI
