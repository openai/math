import OAI.Hierarchy.DescentNodeLocalEnumeration
import OAI.Hierarchy.DescentOriginalSeedArchive

namespace OAI
/-! The original finite scalar enumeration at every site of the input archive. -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentInitialHost DescentSixParty.Chronology Catalyst
noncomputable section
variable {F : Type} [Field F]
def seed {cp ports : ℕ} (X : Approximation F cp ports) (R size : ℕ) (c : (initialGroup X R size).Choice) :
    Local (seedArchive X R size c).bit := fun _=>Fintype.equivFin _

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
