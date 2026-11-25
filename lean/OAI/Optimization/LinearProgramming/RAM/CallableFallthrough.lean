import OAI.Optimization.LinearProgramming.RAM.Code

/-! A fall-through primitive must advance from every source program counter to its
successor. A fixed jump destination and a terminal output each rule this out. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem branchTarget_ne_next (c : Prop) [Decidable c] (yes no : Nat) :
    (if c then yes else no) ≠ max yes no + 1 := by
  have hy := Nat.le_max_left yes no
  have hn := Nat.le_max_right yes no
  split <;> omega

theorem no_fallthrough_branchLT (m t : Memory K) (a b yes no : Nat)
    (h : ∀ pc, execInstr (.branchLT a b yes no) (m.atPC pc) = some (t.atPC (pc+1))) : False :=
  branchTarget_ne_next (m.data a < m.data b) yes no
    (congrArg State.pc (Option.some.inj (h (max yes no))))

theorem no_fallthrough_branchAddrLT (m t : Memory K) (a b yes no : Nat)
    (h : ∀ pc, execInstr (.branchAddrLT a b yes no) (m.atPC pc) = some (t.atPC (pc+1))) : False :=
  branchTarget_ne_next (m.index a < m.index b) yes no
    (congrArg State.pc (Option.some.inj (h (max yes no))))

theorem no_fallthrough_jump (m t : Memory K) (dst : Nat)
    (h : ∀ pc, execInstr (.jump dst) (m.atPC pc) = some (t.atPC (pc+1))) : False := by
  have he : dst = dst+1 := congrArg State.pc (Option.some.inj (h dst))
  omega

theorem no_fallthrough_halt (m t : Memory K) (tag : Nat)
    (h : ∀ pc, execInstr (.halt tag) (m.atPC pc) = some (t.atPC (pc+1))) : False := by
  have he : (some tag : Option Nat) = none := congrArg State.output (Option.some.inj (h 0))
  contradiction

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
