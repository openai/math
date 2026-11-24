import OAI.Computability.VPVNP.PairVertexFrameData

/-! # Preserving the common frame while running the cursor's private stack -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM NodeArguments DFS VertexImage LeafSourceLoad
open scoped Fin.CommRing

variable {w endAddr : ℕ} {R : LeafArena.Regions} {data : Fin 10 → Word w} {offset : Word w}
    {vals : Static 34 → Word w} {s out : Scratch w endAddr}

/-- The leaf writes only its virtual stacks. Each common geometry or cache
operand is physically below their first cell. -/
theorem VertexFrameData.of_below_stack (h : VertexFrameData R data offset vals s)
    (endBefore : endAddr < R.stackBase)
    (preserve : ∀ i : {a : Word w // endAddr ≤ a.val}, i.val.val < R.stackBase → out i = s i) :
    VertexFrameData R data offset vals out := by
  have keep (n : ℕ) (before : n < R.stackBase) :
      rawScratch out (n : Word w) = rawScratch s (n : Word w) := by
    unfold rawScratch
    split
    · exact preserve _ ((Nat.mod_le _ _).trans_lt before)
    · rfl
  refine h.transfer (keep _ endBefore) (fun i => keep _ ?_) (fun j => keep _ ?_)
  · have width := R.hist_before
    have hi := i.isLt
    unfold NativeFrame.frameBase LeafArena.Regions.stackBase
    omega
  · have hi : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
    exact Nat.add_lt_add_left hi _

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
