import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # Fixed width charges of the native private-label counter -/

namespace Hierarchy.DescentSixParty
open DescentCompiler

variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

namespace GadgetNetwork
def privateRate := 2+8*(G.C+2+G.k)
end GadgetNetwork

namespace NativeBranch
open GadgetNetwork
def privateMax (p : ℕ) :=S.length*privateRate G*S.radix*S.initialSites*(S.copies*S.firstWidth G.b p)
end NativeBranch
end Hierarchy.DescentSixParty

end OAI
