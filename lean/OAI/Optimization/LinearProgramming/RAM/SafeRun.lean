import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.EvalWeaken

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Fragment

/-- Preserve the same physical instructions and clock while enlarging the allowed
set of scalars at every visited state. -/
theorem Run.weakenData {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P Q : K→Prop}
    {f : Fragment} {m t : Memory K} {k : ℕ} (h : f.Run P m k t) (all : ∀ y,P y→Q y) : f.Run Q m k t := by
  intro prog pc code
  obtain ⟨l,hl,real⟩:=h prog pc code
  exact ⟨l,hl,real.weaken (fun _ allows j => all _ (allows j))⟩

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
