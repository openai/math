import OAI.Hierarchy.DescentPublicDegreeNumbers

namespace OAI
/-! # Public multiplicative capacity schedule -/
namespace Hierarchy.DescentCompiler
open DescentHostDegree
/-- Public order of the actual multiplicative capacity updates. -/
def ordinaryCapFactors (radix : ℕ) : ℕ→ℕ→List ℕ
  | _,0=>[]
  | start,count+1=>(2^(gainExponent 20 (atRound start))*radix)::ordinaryCapFactors radix (start+1) count

def capPeriod (radix rounds resetGain : ℕ) := ordinaryCapFactors radix 0 rounds++[2^resetGain]

def capCalendar (radix rounds resetGain : ℕ) : ℕ→List ℕ
  | 0=>[]
  | n+1=>capPeriod radix rounds resetGain++capCalendar radix rounds resetGain n


end Hierarchy.DescentCompiler

end OAI
