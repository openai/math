import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentNativeBases

namespace OAI
/-! # The degree-dependent quota of an original period -/
namespace Hierarchy.DescentCompiler
open DescentBaseProfile
def quota (t : ℕ) := atRound t*2^decayExponent (atRound t)+1

end Hierarchy.DescentCompiler

end OAI
