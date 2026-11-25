import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

variable {K : Type*}

private theorem atPC_data (m : Memory K) (pc : ℕ) : (m.atPC pc).data = m.data := rfl
private theorem atPC_index (m : Memory K) (pc : ℕ) : (m.atPC pc).index = m.index := rfl
private theorem atPC_memory (m : Memory K) (pc : ℕ) : (m.atPC pc).memory = m := rfl
private theorem atPC_putData (m : Memory K) (pc d : ℕ) (x : K) :
    (m.atPC pc).putData d x = (m.putData d x).atPC (pc+1) := rfl
private theorem atPC_putIndex (m : Memory K) (pc d n : ℕ) :
    (m.atPC pc).putIndex d n = (m.putIndex d n).atPC (pc+1) := rfl

attribute [local simp] atPC_data atPC_index atPC_memory atPC_putData atPC_putIndex

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Ordinary arithmetic, copies, and both kinds of indirect access are simulated by
one instruction each, including division's requirement that the divisor be nonzero. -/
theorem instr_eval_of_cost_one (P : K → Prop) (callee : Memory K) (hc : callee.AllData P)
    (i : Instr) (hi : instrCost i = 1) {m t : Memory K}
    (h : Block.Eval (Memory.AllData P) (.op i) m 1 t) :
    Block.Eval (Memory.AllData P) (instr i) (memory callee m) (instrCost i) (memory callee t) := by
  cases h with
  | op hm ht hstep =>
    have hm' := allData callee m hc hm
    have ht' := allData callee t hc ht
    cases i <;> simp [instrCost] at hi
    case div d a b =>
      have hn : m.data b ≠ 0 := by
        intro hz
        have hs := hstep 0
        simp [execInstr,hz] at hs
      have hw : m.putData d (m.data a / m.data b) = t := by
        simpa [execInstr,hn] using congrArg (Option.map State.memory) (hstep 0)
      subst t
      exact .op hm' ht' (fun pc => by simp [execInstr,hn])
    all_goals
      have hw := congrArg (Option.map State.memory) (hstep 0)
      simp [execInstr] at hw
      subst t
      exact .op hm' ht' (fun pc => by simp [execInstr])

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
