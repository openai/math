import OAI.Optimization.LinearProgramming.PrimalDual.JointEncoder
import OAI.Optimization.LinearProgramming.PrimalDual.JointStaging
import OAI.Optimization.LinearProgramming.RAM.RAMFrame

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace JointRAM

open RAM

/-- Address registers from 32 upward are reserved for the caller. Both blocks have a
fixed syntactic ceiling even though each can write to a dynamically located scalar buffer. -/
def firstFree : Nat := 32

theorem encode_indexWritesBelow : encode.indexWritesBelow firstFree = true := by decide

theorem stageWindows_indexWritesBelow : stageWindows.indexWritesBelow firstFree = true := by decide

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m t : Memory K} {safe : Memory K → Prop} {k i : Nat}

theorem encode_preserves_high (h : Block.Eval safe encode m k t) (hi : firstFree ≤ i) :
    t.index i = m.index i := h.index_frame encode_indexWritesBelow hi

theorem stageWindows_preserves_high (h : Block.Eval safe stageWindows m k t) (hi : firstFree ≤ i) :
    t.index i = m.index i := h.index_frame stageWindows_indexWritesBelow hi

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI
