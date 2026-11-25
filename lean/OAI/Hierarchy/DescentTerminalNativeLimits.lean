import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Public capacities for the full-incidence terminal row packing -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler
variable {F : Type} [Field F]

def localLimit (G : PoweredGadget F) (S : AtomSchedule) := 2*G.b*2^(8+S.capGain*S.length)
def binLimit {k : ℕ} (S : AtomSchedule) := 3*(S.groupCount S.length*2^k)+6

end Hierarchy.DescentSixParty.NativeBranch

end OAI
