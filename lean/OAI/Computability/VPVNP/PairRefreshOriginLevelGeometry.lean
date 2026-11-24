import OAI.Computability.VPVNP.PairRefreshSelectedPackets
import OAI.Computability.VPVNP.PairVertexSelectedDesc
import OAI.Computability.VPVNP.PairVertexFrameData

/-!
# Physical packet geometry at a selected refresh level

The pointer following the old rows is the parent used by the native refresh
reader. Its output packet carries the same independent half-wire assignment.
The selected descendant list and packet format apply to every placed input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles LocalHistory NetworkKernel NodeArguments TreeDecode
open VertexImage DFS
open scoped Fin.CommRing
set_option quotPrecheck false

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n hist w start positions width : ℕ)

local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => selected B f hf blocks budget X branch
local notation "rows" => tagWords B.recordLimit (tags₀)
local notation "pos" => layerBase B.recordLimit first (tags₀)
local notation "format₀" => SelectedPacketFormat B f hf blocks budget X branch first
local notation "desc₀" => selectedDesc B f hf blocks budget X branch first
variable (room : Rooms n hist w start positions blocks ⟨leafLayer (siteOrder X), .cursor⟩
      (executeLevels B f hf blocks budget X branch))
    (x : Row (executeLevels B f hf blocks budget X branch))
local notation "i₀" => x.val.1
local notation "u₀" => x.val.2
local notation "v₀" => (passes)[i₀]
local notation "R₀" => rowSite n hist w start positions blocks width (leaf₀) passes room x
local notation "reader₀" => originReader B f hf (v₀).origin (v₀).term
local notation "nextBase" => TraversalRows.address B.recordLimit
  ((pos) (i₀).val) (siteOrder (v₀).input).length
local notation "ptr" => sitePointers B.recordLimit nextBase (ShrinkRoleDirectory.outputOrder (v₀))
local notation "src" => (fun u z => Packet.mk (sitePointers B.recordLimit ((pos) (i₀).val)
  (siteOrder (v₀).input) u).1 (packed (v₀).input u z))
local notation "head₀" => (fun z => Packet.mk ((ptr) u₀).1
  (pullBits ((v₀).pass.output_eq (v₀).term) (packed ((v₀).pass.next (v₀).term)) u₀ z))
local notation "newHalf" => halfEquiv (v₀) u₀ x.property

/-- The target pointer calculated by the selected level checker. -/
theorem level_parent : ((ptr) u₀).1 = (R₀).parent := by
  have after := selected_level_bases B f hf blocks budget X branch first i₀
  have ptrEq := congrArg (fun b => (sitePointers B.recordLimit b
    (ShrinkRoleDirectory.outputOrder (v₀)) u₀).1) after.symm
  exact ptrEq.trans (parent_eq n hist w start positions blocks width (leaf₀) passes room x).symm

set_option maxHeartbeats 1500000 in
-- The selected term carries dependent input and output networks.
/-- The packet consumed at the selected row has the exact address and packed
output-half order of the local refresh hook. -/
theorem level_packet (z : ((v₀).pass.step.term (v₀).term).output.Half u₀) :
    (head₀) z = ⟨(R₀).parent,packed (R₀).nextState (R₀).newerSite ((newHalf) z)⟩ := by
  exact congrArg₂ Packet.mk
    (level_parent B f hf blocks budget X branch n hist w start positions width room x)
    (halfEquiv_packed (v₀) u₀ x.property z)

set_option maxHeartbeats 1500000 in
-- The selected term carries dependent input and output networks.
/-- The descendant list is the concatenation of the ordered child subtrees,
for any independent placed old halves in the selected term. -/
theorem level_children_shape
    (a : Placed ((v₀).pass.step.term (v₀).term).place (v₀).input.network.Half u₀) :
    (desc₀) (R₀).parent =
      (TreeDecode.children (reader₀) (src) u₀ a).flatMap (subtreeAddresses desc₀) := by
  have atRow := parent_eq n hist w start positions blocks width (leaf₀) passes room x
  have shape := selectedDesc_level B f hf blocks budget X branch first i₀ u₀
  have addresses := children_addresses (reader₀) (src) (fun u =>
    (sitePointers B.recordLimit ((pos) (i₀).val) (siteOrder (v₀).input) u).1)
    (fun _ _ => rfl) (desc₀) u₀ a
  exact (congrArg (desc₀) atRow).trans (shape.trans addresses.symm)

set_option maxHeartbeats 1500000 in
-- The selected term carries dependent input and output networks.
/-- Each placed child has the packet format of its actual selected input row. -/
theorem level_children_format
    (a : Placed ((v₀).pass.step.term (v₀).term).place (v₀).input.network.Half u₀)
    {q : Packet} (mem : q ∈ TreeDecode.children (reader₀) (src) u₀ a) : (format₀) q := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
  exact (selected_format B f hf blocks budget X branch first).1 i₀ _ ⟨_,_,rfl⟩

/-- All selected packets, including unrelated pending siblings, lie in the
same physical row interval as the selected hook. -/
theorem level_node_lt (q : Packet) (format : (format₀) q) : q.node < (R₀).rowEnd := by
  change q.node < first + rows
  rw [tagWords,selected_layers]
  exact selected_packet_node B f hf blocks budget X branch first format

/-- Converting the physical parent address to a machine word loses no bits.
The selected refresh room places the entire argument arena below the cache. -/
theorem level_parent_val : ((R₀).parent : Word w).val = (R₀).parent := by
  have bound := (R₀).room.parentBound
  have rowBefore : (R₀).rowEnd ≤ (R₀).regions.histBase :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_add_left ..)
  have histBefore : (R₀).regions.histBase ≤ (R₀).regions.cacheBase :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have endFit := (rowBefore.trans histBefore).trans_lt (R₀).room.capacity.room
  exact Nat.mod_eq_of_lt (bound.trans endFit)

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
