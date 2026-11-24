import OAI.Computability.VPVNP.PairVertexFrameData

/-! # Physical leaf domain for a stored cursor packet -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM CursorRouting CursorNetwork DFS NodeArguments
open TreeDecode LeafHandler LocalHistory NetworkKernel CompressorRecords
open scoped Fin.CommRing

/-- A typed first-layer packet and its resident private frame provide all
the physical inputs required by the leaf reader, on any pending suffix. -/
theorem domain_of_packet {w endAddr : ℕ} {L : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q s)
    {b l e degree pad : ℕ} (hD : 1 < b+l) (hd : 2+pad = 2^degree)
    {R : LeafArena.Regions} {data : Fin 10 → Word w} {offset : Word w} {cap : ℕ}
    {q : Packet} {saved : Scratch w endAddr}
    (typed : ∃ u z, q = ⟨(TraversalRows.sitePointers cap ((addressFields data) .base).val
      (siteOrder (LeafArguments.state hD hd (2^e) w)) u).1, packed (LeafArguments.state hD hd (2^e) w) u z⟩)
    (within : q.node < R.nodes) (word : q.node < 2^w)
    (fits : q.Fits R.arguments w endAddr) (stored : q.Stored R.arguments saved)
    (frame : VertexFrameData R data offset (LeafVisit.cacheWords D (b+l) e) saved) :
    Domain (e := e) data D hD hd R cap (NativeFrame.frameBase R) (q.node : Word w) saved := by
  have exactNode : (q.node : Word w).val = q.node := Nat.mod_eq_of_lt word
  refine ⟨⟨by rw [exactNode]; exact within,frame.cached,?_⟩,frame.record⟩
  obtain ⟨u,z,rfl⟩ := typed
  obtain ⟨v,rfl⟩ := (lanePositions (cursorCoordinateLabels b l)).surjective u
  refine ⟨v,z,exactNode,?_,?_⟩
  · rw [exactNode]
    exact fits
  · rw [exactNode]
    exact stored

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
