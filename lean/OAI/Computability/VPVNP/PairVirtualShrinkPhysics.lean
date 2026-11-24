import OAI.Computability.VPVNP.PairVirtualShrinkRowCost
import OAI.Computability.VPVNP.PairVertexSelectedRoleLayout
import OAI.Computability.VPVNP.PairSelectedPacketGeometry

/-! # Addresses and public tags for shrinking in the linked vertex memory

All site readers at one selected vertex see the same role image. Its tag
offset is the selected row count plus the total final-wire width. The
private buffers, histogram and node array use the corresponding packed
terminal allocation, including after previous vertices have updated their
counter words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VirtualShrink

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary Compression CompressorRecords
open DescriptorSpace TerminalProgram TraversalRows TraversalRoles NodeArguments LocalHistory

variable {k A : Type} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) (G : PairStages.Group)
    (n : ℕ) {labels : ℕ} (order : B.Entry ≃ Fin labels) {lanes : ℕ} (T : ℕ)
    (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (m : Memory G.w)

local notation "pub" => terminalOperands G
local notation "L" => BlockProgram.layout B (Fin.val (pub 2)) X.positions T
local notation "tags" => selected B f hf T hT X z
local notation "passes" => executeLevels B f hf T hT X z
local notation "rows" => selectedLayers B f hf T hT X z
local notation "base" => endAddress L
local notation "size" => tagWords B.recordLimit tags
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf T hT X) z)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n (base+size) labels
local notation "hdr" => vertexHeader G

/-- The selected shrinking rows' budget, their published role words in linked memory,
and the address bounds for the role table, vertex header, frames, histogram and nodes. -/
structure Physics : Prop where
  budget : ShrinkRole.RowBudget B order X n G.w T
  rowEq : size = words B.recordLimit rows
  published : Reads G.w m (size+width) B.recordLimit base tags
  codes : 2 < 2^G.w
  tagEnd : size+width+base+size ≤ (hdr).val
  headerFit : (hdr).val+31 < 2^G.w
  start : n ≤ (area).arguments.start
  stride : frameStride (slotDegree S) n ≤ (area).arguments.stride
  histFit : (area).histBase ≤ 2^G.w
  nodes : base+words B.recordLimit rows ≤ (area).nodes
  layerFit : layerBase B.recordLimit base tags ((passes).length+1) < 2^G.w

theorem physics {baseBits laneBits ordinal : ℕ} {tab : Fin (L).shape.tables}
    {calendar reference : Memory G.w} {bits : Fin width → Bool}
    (budget : ShrinkRole.RowBudget B order X n G.w T)
    (pack : VertexPacked G L B.recordLimit tags width)
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar reference bits)
    (later : LinkedVertexMemory G reference ordinal m)
    (stack : (area).stackBase ≤ 2 ^ G.w) : Physics B f hf G n order T hT X z m := by
  have rowEq : size = words B.recordLimit rows :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have tagsAt : Reads G.w m (size+width) B.recordLimit base tags := by
    apply pack.roleWords later
    rw [rowEq]; exact entry.roles
  have head := pack.room
  have region := pack.arena
  have hist : (area).histBase ≤ (area).stackBase :=
    (Nat.le_add_right _ labels).trans ((Nat.le_add_right _ (n^5)).trans (Nat.le_add_right _ 38))
  refine ⟨budget,rowEq,tagsAt,by omega,by omega,by omega,le_rfl,le_rfl,hist.trans stack,?_,?_⟩
  · change base + words B.recordLimit rows ≤ base+size
    rw [rowEq]
  · rw [TreeDecode.selected_endBase,← rowEq]
    have mod := (hdr).isLt
    omega

end PairSimulation.VirtualShrink

end VPVNP
end Computability
end OAI
