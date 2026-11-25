import OAI.Optimization.LinearProgramming.RAM.CallableOddSingle
import OAI.Optimization.LinearProgramming.RAM.CallableOddCounter
import OAI.Optimization.LinearProgramming.RAM.CallableFallthrough

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Simulate a fall-through caller primitive in the odd bank, with its exact charged
cost. The entire even callee bank and the scalar invariant are preserved. -/
theorem instr_eval (P : K → Prop) (callee : Memory K) (hc : callee.AllData P)
    (i : Instr) {m t : Memory K} (h : Block.Eval (Memory.AllData P) (.op i) m 1 t) :
    Block.Eval (Memory.AllData P) (instr i) (memory callee m) (instrCost i) (memory callee t) := by
  by_cases hp : instrCost i = 1
  · exact instr_eval_of_cost_one P callee hc i hp h
  cases h with
  | op hm _ hstep =>
    cases i <;> simp [instrCost] at hp
    case incr d a =>
      have hw : m.putIndex d (m.index a+1) = t := congrArg State.memory (Option.some.inj (hstep 0))
      subst t
      exact incr_eval P callee m hc hm d a
    case decr d a =>
      have hw : m.putIndex d (m.index a-1) = t := congrArg State.memory (Option.some.inj (hstep 0))
      subst t
      exact decr_eval P callee m hc hm d a
    case branchLT a b yes no => exact (no_fallthrough_branchLT m t a b yes no hstep).elim
    case branchAddrLT a b yes no => exact (no_fallthrough_branchAddrLT m t a b yes no hstep).elim
    case jump dst => exact (no_fallthrough_jump m t dst hstep).elim
    case halt tag => exact (no_fallthrough_halt m t tag hstep).elim

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
