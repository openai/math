import OAI.Computability.VPVNP.PairVertexActiveRoot
import OAI.Computability.VPVNP.PairTreeFrontierBudget
import OAI.Computability.VPVNP.PairSimulationLeafRoleHandler

/-! # The geometry and validator words retained throughout one vertex call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM NodeArguments DFS VertexImage LeafSourceLoad
open scoped Fin.CommRing

variable {w endAddr : ℕ}

/-- These words are shared by all roles of the current vertex. The argument
buffers and running histogram occupy their own private intervals. -/
structure VertexFrameData (R : LeafArena.Regions) (data : Fin 10 → Word w)
    (offset : Word w) (vals : Static 34 → Word w) (s : Scratch w endAddr) : Prop where
  record : LeafGeometryLoad.Stored endAddr (NativeFrame.frameBase R) (rawScratch s) data
  resident : ResidentGeometry s ((NativeFrame.frameBase R : ℕ) : Word w) offset
    (R.histBase : Word w)
  cached : Cached R.cacheBase (rawScratch s) vals

variable {R : LeafArena.Regions} {data : Fin 10 → Word w} {offset : Word w}
    {vals : Static 34 → Word w} {s out : Scratch w endAddr}

private theorem word_add_nat (x i : ℕ) : ((x+i : ℕ) : Word w) = (x : Word w)+(i : Word w) :=
  Nat.cast_add ..

/-- An arbitrary kernel can update its child arguments, temporary words and
histogram while retaining the three parts of the common private frame. -/
theorem VertexFrameData.transfer (h : VertexFrameData R data offset vals s)
    (pointer : rawScratch out (endAddr : Word w) = rawScratch s (endAddr : Word w))
    (fields : ∀ i : Fin 12, rawScratch out ((NativeFrame.frameBase R+i.val : ℕ) : Word w) =
      rawScratch s ((NativeFrame.frameBase R+i.val : ℕ) : Word w))
    (cache : ∀ j : Static 34, rawScratch out ((R.cacheBase+j.offset : ℕ) : Word w) =
      rawScratch s ((R.cacheBase+j.offset : ℕ) : Word w)) :
    VertexFrameData R data offset vals out := by
  refine ⟨⟨pointer.trans h.record.pointer,
    fun i => (fields (i.castLE (by decide))).trans (h.record.values_at i)⟩,
    ⟨h.resident.endFit,h.resident.roleAbove,h.resident.histAbove,
      pointer.trans h.resident.pointer,?_,?_⟩,
    fun j => (cache j).trans (h.cached j)⟩
  · have cell : rawScratch out ((NativeFrame.frameBase R+10 : ℕ) : Word w) =
        rawScratch s ((NativeFrame.frameBase R+10 : ℕ) : Word w) := fields 10
    rw [word_add_nat, Nat.cast_ofNat] at cell
    exact cell.trans h.resident.role
  · have cell : rawScratch out ((NativeFrame.frameBase R+11 : ℕ) : Word w) =
        rawScratch s ((NativeFrame.frameBase R+11 : ℕ) : Word w) := fields 11
    rw [word_add_nat, Nat.cast_ofNat] at cell
    exact cell.trans h.resident.histogram

/-- The actual bootstrap and gather produce the private frame in the same
scratch on which the role decoders run. -/
theorem frame_of_root {S : Part → Segment} {p r : ℕ} {A : Placement S p r} {cfg : Config w p r}
    {ordinal endWord roleWord : Word w} {q : Packet} {fields : Fin 12 → Word w}
    (root : ActiveRootState A cfg ordinal endWord roleWord R q data fields vals)
    (offsetAt : fields 10 = offset) (histAt : fields 11 = (R.histBase : Word w))
    (above : endWord.val ≤ NativeFrame.frameBase R)
    (frameFit : NativeFrame.frameBase R + 12 ≤ 2 ^ w) (beforeCache : endWord.val ≤ R.cacheBase)
    (cacheFit : R.cacheBase + 38 ≤ 2 ^ w) :
    VertexFrameData R data offset vals (scratch endWord.val cfg.privateMem) := by
  have geom := root.resident.residentGeometry above frameFit
  rw [offsetAt,histAt] at geom
  refine ⟨⟨geom.pointer,?_⟩,geom,root.resident.cacheScratch beforeCache cacheFit⟩
  intro i
  have hf : NativeFrame.frameBase R+i.val < 2 ^ w := by have := i.isLt; omega
  have live : endWord.val ≤ ((NativeFrame.frameBase R+i.val : ℕ) : Word w).val := by
    rw [Fin.val_natCast,Nat.mod_eq_of_lt hf]
    exact above.trans (Nat.le_add_right _ _)
  rw [rawScratch,dite_eq_left live]
  exact root.resident.geometry.values_at i

/-- At the root the selected histogram is still zero. Its full remaining
subtree charge establishes the invariant required by every later prefix. -/
theorem budget_of_root {S : Part → Segment} {p r : ℕ} {A : Placement S p r} {cfg : Config w p r}
    {ordinal endWord roleWord : Word w} {q : Packet} {fields : Fin 12 → Word w}
    (root : ActiveRootState A cfg ordinal endWord roleWord R q data fields vals)
    (offsetAt : fields 10 = offset) (histAt : fields 11 = (R.histBase : Word w))
    (above : endWord.val ≤ R.histBase) (frameFit : NativeFrame.frameBase R + 12 ≤ 2 ^ w)
    (cacheFit : R.cacheBase + 38 ≤ 2 ^ w) (format : Packet → Prop) (type : format q)
    (desc : ℕ → List ℕ) (distinct : (subtreeAddresses desc q).Nodup)
    {L : Type} (order : Fin R.histWords ≃ L) (nodeCap limit : ℕ)
    (capacity : (subtreeAddresses desc q).length * nodeCap ≤ limit) :
    Budgeted R.arguments format (VertexFrameData R data offset vals) desc
      (privateHistogram order R.histBase) nodeCap limit [q]
      (scratch endWord.val cfg.privateMem) := by
  have frameAbove : endWord.val ≤ NativeFrame.frameBase R := above.trans (Nat.le_add_right ..)
  have beforeCache : endWord.val ≤ R.cacheBase := frameAbove.trans R.hist_before
  exact Budgeted.singleton (Frontier.singleton
    (frame_of_root root offsetAt histAt frameAbove frameFit beforeCache cacheFit)
    type root.fits root.stored distinct)
    (root.resident.zeroHistogram order above (by omega)) capacity

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
