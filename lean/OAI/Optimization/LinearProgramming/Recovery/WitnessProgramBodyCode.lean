import OAI.Optimization.LinearProgramming.Recovery.MaskedProgramCode
import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveCode
import OAI.Optimization.LinearProgramming.Recovery.WitnessTableCore
import OAI.Optimization.LinearProgramming.Recovery.PublishOdd
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf

/-! Shared fixed code for constructing, solving, and publishing a normalized witness. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

open RAM RAM.Callable

def body : Fragment := .seq (Odd.leaf MaskedInput.program)
  (.seq (Odd.leaf WitnessTable.block) (.seq WitnessSolve.program (Fragment.ofBlock (Publish.fromOdd 0))))

instance body_fixedAccess : Fragment.FixedAccess body := by
  unfold body Odd.leaf
  infer_instance

noncomputable def bodyTime (h n : ℕ) : ℕ :=
  4*MaskedInput.programTime h n + (4*WitnessTable.clockPolynomial.eval (h+n) +
    (WitnessSolve.time n (h+n+1) (WitnessTable.capacity h n) + Publish.oddTime n))

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
