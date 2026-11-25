import OAI.Optimization.LinearProgramming.RAM.CallableOddBlock
import OAI.Optimization.LinearProgramming.RAM.CallableBase

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

/-- Execute an ordinary logical caller block while leaving the native callee bank intact. -/
def leaf (b : Block) : Fragment := Fragment.ofBlock (block b)

theorem leaf_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (callee : Memory K) (hc : callee.AllData P)
    {b : Block} {m t : Memory K} {k : ℕ} (h : Block.Eval (Memory.AllData P) b m k t) :
    (leaf b).Run P (memory callee m) (4*k) (memory callee t) := by
  obtain ⟨l,hl,run⟩ := block_eval P callee hc h
  exact (Fragment.Run.ofBlock run).mono hl

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
