import OAI.Optimization.LinearProgramming.Recovery.PrimalHeader
import OAI.Optimization.LinearProgramming.Recovery.PrimalTableCode
import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveCode
import OAI.Optimization.LinearProgramming.Recovery.PublishOdd

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PrimalOutput
open RAM RAM.Callable Geometry

def program : Fragment:=.seq (Odd.leaf (.seq headerBlock assemble)) (.seq WitnessSolve.program (.ofBlock (Publish.fromOdd 0)))
noncomputable def programTime (m d cap limit : ℕ) := 4*((headerTime.eval limit)+assembleTime m d)+
  (WitnessSolve.time d m cap+Publish.oddTime d)

instance program_fixedAccess : Fragment.FixedAccess program := by
  unfold program Odd.leaf
  infer_instance

end PrimalOutput
end Recovery
end LinearProgramming
end Optimization
end OAI
