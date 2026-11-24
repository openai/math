import OAI.Computability.VPVNP.PairPendingArguments
import OAI.Computability.VPVNP.PairTerminalGatherGeometry
import OAI.Computability.VPVNP.PairTerminalLayout

/-!
# The typed root argument after the native terminal gather

The root packet records the selected vertex's outgoing and incoming half-wire
bits in DFS order. Its private interval starts at the destination computed by
the terminal gather and ends before the common histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexRootPacket

open BurstRAM PrivateRAM Compression TerminalRootGather
open scoped Fin.CommRing

variable {a g w p r : ℕ}

/-- The root argument packet pairing the final site's DFS address with its packed half-wire
assignment from the shared bit array. -/
noncomputable def packet (X : State a g) (L : Layout) (u : X.network.Site)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) : NodeArguments.Packet :=
  ⟨L.root, NodeArguments.packed X u (TerminalGatherGeometry.half X f u)⟩

/-- The physical frame stride covers both half-wire lists of the terminal
vertex, including repeated endpoints of a loop. -/
theorem length_le_stride (X : State a g) (L : Layout) (u : X.network.Site)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) (degree : ℕ)
    (deg : 2^a ≤ degree) (width : X.maxWireWidth ≤ L.n) :
    (packet X L u f).bits.length ≤ NodeArguments.frameStride degree L.n :=
  (NodeArguments.packed_length_le X u _).trans
    ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 deg) width).trans (Nat.le_succ _))

variable {X : State a g} {L : Layout} {u : X.network.Site} {m : Memory w}

/-- Translate the private-memory equality produced by the installed gather
into the packet invariant at the first DFS instruction. -/
theorem of_gather (num : TerminalGatherGeometry.Numbering X L u) (rows : TerminalGatherGeometry.Rows X L m)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, m (L.wires+i.val) = PrivateFields.bitValue w (f i)) (fit : L.Fits m)
    (R : LeafArena.Regions) (start : L.n = R.arguments.start) (stride : L.stride = R.arguments.stride)
    (root : L.root < R.nodes) (size : (packet X L u f).bits.length ≤ R.arguments.stride)
    (c out : Config w p r)
    (native : out.privateMem = Layout.placed L.dest (L.packet m) c.privateMem) :
    let q := packet X L u f
    q.Fits R.arguments w L.n ∧ q.Stored R.arguments (DFS.scratch L.n out.privateMem) ∧
      R.arguments.base q.node + q.bits.length ≤ R.histBase := by
  let q := packet X L u f
  have dest : L.dest = R.arguments.base q.node := by
    change L.n + L.root*L.stride = R.arguments.start + L.root*R.arguments.stride
    rw [start, stride]
  have len : (L.packet m).length = q.bits.length := by
    rw [TerminalGatherGeometry.packet_eq num rows f bits, List.length_map]
    rfl
  have below := (Nat.add_le_add_left size (R.arguments.base q.node)).trans (R.node_before root)
  have hq : q.Fits R.arguments w L.n :=
    ⟨start ▸ Nat.le_add_right .., size, by simpa only [dest,len] using fit.destEnd.le⟩
  have stored : out.privateMem = PrivateFields.storeBits (R.arguments.base q.node) q.bits c.privateMem := by
    rw [native, TerminalGatherGeometry.placed_packet num rows f bits fit, dest]
    rfl
  refine ⟨hq, ?_, below⟩
  intro i
  let addr : Word w := ((R.arguments.base q.node + i.val : ℕ) : Word w)
  have value : addr.val = R.arguments.base q.node + i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le hq.2.2)
  have high : L.n ≤ addr.val := value ▸ hq.1.trans (Nat.le_add_right ..)
  change NodeArguments.rawScratch (DFS.scratch L.n out.privateMem) addr = _
  rw [NodeArguments.rawScratch, dite_eq_left high, DFS.scratch, stored]
  exact PrivateFields.storeBits_read (R.arguments.base q.node) q.bits c.privateMem hq.2.2 i

end PairSimulation.VertexRootPacket

end VPVNP
end Computability
end OAI
