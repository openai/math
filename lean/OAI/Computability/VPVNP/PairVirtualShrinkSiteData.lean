import OAI.Computability.VPVNP.PairVirtualShrinkCapacity
import OAI.Computability.VPVNP.PairShrinkPhysicalSiteData

/-!
# The virtual pair's selected shrinking operands

The per-site capacity on the tagged traversal and the packed compressor payload
refer to the same node reservation. Together they furnish every operand of the
physical shrinking reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program.VirtualShrink

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open PairSimulation PairSimulation.ShrinkRole LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open NodeArguments NodeArguments.ChildScan TraversalControllerInputs
open scoped Fin.CommRing

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
  {G : Group} {n T limit lanes : ℕ} (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

attribute [local irreducible] ShrinkRoleDirectory.occurrence BlockProgram.layout
  BlockSchedule.Templates.execute StateExecution.finalState executeLevels

set_option quotPrecheck false
local notation "pub" => terminalOperands G
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "tags" => TraversalRoles.selected B f hf T hT X z

variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
  {baseBits laneBits ord : ℕ} {calendar reference phy : Memory G.w}
  {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
  (history : SelectedPayloadHistory.Past B f hf
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    (CompiledResident.payload B f hf (terminalOperands G 2) X.positions T n)
    (executeLevels B f hf T hT X z) calendar)
  (entry : TerminalProgram.VertexEntry (w := G.w) B f hf T hT X z
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T) table baseBits laneBits
    (terminalOperands G) calendar reference bits)
  (packed : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    B.recordLimit (TraversalRoles.selected B f hf T hT X z)
    (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
  (frame : LinkedVertexMemory G reference ord phy)
  (width : MapConstants.widthThreshold B.shrink ≤ G.w)
  (fits : ∀ x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z), ∀ m,
    canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection (w := G.w)
      (Fintype.card B.Entry) n
      (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T) +
        words B.recordLimit (selectedLayers B f hf T hT X z))
      (layerBase B.recordLimit (endAddress (BlockProgram.layout B (terminalOperands G 2).val
        X.positions T)) (TraversalRoles.selected B f hf T hT X z) x.val.1.val) limit m)
  (x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z))

local notation "o" => x.occurrence
local notation "site" => physicalSiteBank B f hf hT X z history entry packed frame width fits x
local notation "id" => VertexImage.RoleDomains.siteId B f hf T hT X z x
set_option maxHeartbeats 1500000 in
-- The two row counts index the same selected pass and its dependent job and packet types.
/-- The true physical operand bank of the popped row satisfies its complete site
contract at every later vertex in the terminal scan. -/
theorem Capacity.siteData {p r : ℕ} (M : Machine G.w p r 11) (publicWords : M.publicData = pub)
    (capacity : Capacity B f hf G n T hT X z x) :
    CanonicalSiteData site M f hf T hT X z x.val.1 id (endAddress D) := by
  let j := x.val.1
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame j (o).selected
  have same : tagWords B.recordLimit tags = words B.recordLimit (selectedLayers B f hf T hT X z) :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have hidden := capacity.maps.hidden phy payload
  have free := capacity.hiddenSpace.capacity
  have room := capacity.rows.frameRoom
  rw [same] at hidden free room
  have older := capacity.rows.earlier
  rw [shrinkSiteOrdinal_eq B (o).i (o).state (o).selection (o).site] at older
  exact physicalSiteData B f hf hT X z history entry packed frame width fits x M publicWords
    capacity.rows.wire room older capacity.hiddenSpace.width free hidden

end FixedProgramDiagonal.Program.VirtualShrink

end VPVNP
end Computability
end OAI
