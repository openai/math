import OAI.Optimization.LinearProgramming.Compression.ServicePrepareProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceInspectProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceInvoke
import OAI.Optimization.LinearProgramming.Compression.ServiceReturn
import OAI.Optimization.LinearProgramming.Compression.PhysicalRestartCode
import OAI.Optimization.LinearProgramming.Compression.BinaryFramedReturn

/-! One public serving ROM for the rational and real minor services. The field-specific
proofs certify this same sequence of literal RAM instructions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM RAM.Callable GeneratorTable

namespace ServiceDecision

def replyTag : Option ℚ → ℕ
  | none => 1
  | some _ => 0

theorem replyTag_lt (r : Option ℚ) : replyTag r < 2 := by
  cases r with
  | none => exact Nat.lt_succ_self 1
  | some _ => exact Nat.zero_lt_succ 1

noncomputable def decision (p : Program) (time : Polynomial ℕ) : Fragment :=
  .seq (.ofBlock (ServicePrepare.block time (ServiceInvoke.numerical p).localBudget))
    (.seq (.ofBlock (.op (.addrConst 15 1))) (ServiceInvoke.numerical p))

end ServiceDecision

namespace ServiceBranch

def finish : Fragment :=
  .branch (.addrLT 11 15)
    (.seq (.ofBlock restorePublishedReply) (.ofBlock (ServiceReturn.mark true)))
    (.seq (.ofBlock physicalRestartPost) (.ofBlock (ServiceReturn.mark false)))

end ServiceBranch

/-- All three natural parameters are global literals of the compiled finite program.
The resulting instruction stream is fixed before the input dimensions and matrices. -/
def serveWith (numerical : Program) (coefficient exponent constant : ℕ) : Program :=
  let inspect := Fragment.ofBlock inspectAndGather
  let prepare := Fragment.ofBlock (ServicePrepare.withParameters coefficient exponent constant)
  let num := Fragment.seq prepare
    (.seq (.ofBlock (.op (.addrConst 15 1))) (ServiceInvoke.numerical numerical))
  ServiceReturn.program (.seq inspect (.seq num ServiceBranch.finish))

/-- A fixed time certificate supplies the finite clearing-window parameters. -/
noncomputable def compiledServe (p : Program) (time : Polynomial ℕ) : Program :=
  serveWith p (ServiceBudget.coefficient time) (ServiceBudget.exponent time)
    ((ServiceInvoke.numerical p).localBudget+114)

end Compression
end LinearProgramming
end Optimization
end OAI
