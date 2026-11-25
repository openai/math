import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveSize
import OAI.Optimization.LinearProgramming.Elimination.UniformSolve
import OAI.Optimization.LinearProgramming.Recovery.WitnessExportCore
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess

/-! The fixed rectangular solver fragment and its physical caller-window export. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessSolve

open RAM RAM.Callable

def call : Fragment :=
  Fragment.stage (.invoke Elimination.uniformSolveProgram 1 (Odd.sink (.index 1)))

def program : Fragment := .seq call WitnessExport.program

def time (d m cap : ℕ) : ℕ := callTime d m cap + WitnessExport.time d

instance program_fixedAccess : Fragment.FixedAccess program := by
  unfold program call Fragment.stage
  infer_instance

end WitnessSolve
end Recovery
end LinearProgramming
end Optimization
end OAI
