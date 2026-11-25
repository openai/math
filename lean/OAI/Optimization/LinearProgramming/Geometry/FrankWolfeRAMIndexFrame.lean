import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAM
import OAI.Optimization.LinearProgramming.RAM.RAMFrame
import OAI.Optimization.LinearProgramming.Games.RAMFrame

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM

/-- All direct address-register destinations in the fixed geometric label block are below 35. -/
theorem labelBlock_indexWritesBelow : labelBlock.indexWritesBelow 35 = true := rfl

theorem labelBlock_index_frame {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {m t : Memory K} {k : Nat}
    (h : Block.Eval safe labelBlock m k t) {r : Nat} (hr : 35 ≤ r) :
    t.index r = m.index r :=
  h.index_frame labelBlock_indexWritesBelow hr

/-- Every direct write to the address bank in this subroutine targets one of these registers. -/
def labelIndexScratch : List Nat := [20,21,22,24,26,27,30,31,32]

theorem labelBlock_index_frame_outside {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {m t : Memory K} {k : Nat}
    (h : Block.Eval safe labelBlock m k t) {r : Nat} (hr : r ∉ labelIndexScratch) :
    t.index r = m.index r := by
  apply Games.OrbitRAM.block_frame h (Games.OrbitRAM.noIndexWrite r) (fun s => s.index r)
  · intro i s u hi run
    exact Games.OrbitRAM.index_unchanged r hi (run 0)
  · repeat' apply And.intro
    all_goals first | exact True.intro | (rintro rfl; exact hr (by decide))

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
