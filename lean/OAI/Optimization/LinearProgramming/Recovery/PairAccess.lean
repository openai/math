import OAI.Optimization.LinearProgramming.Recovery.PairBuilderProgram
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess

/-! The pair builder's isolated normal calls and actual leaf blocks have fixed access operands. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Callable

instance program_fixedAccess (rev : Bool) : Fragment.FixedAccess (program rev) := by
  unfold program firstCall firstExport residualCall residualExport lastCall lastExport «meta» header normalCall receive copyRows Fragment.stage Odd.leaf
  infer_instance

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
