import OAI.Computability.VPVNP.PairShrinkRoleCompiledSite
import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairVertexCompiledPayload

/-!
# Physical shrinking sites for the terminal traversal

The row's chronological origin selects the actual compressor payload and its
output site. The address, owner, stage number, hidden fields and matrix row
in each parser therefore belong to the branch traversed by this terminal call.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
  {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
  (z : (B.execute f hf T hT X).Choices) {G : Group} {n limit : ℕ}

attribute [local irreducible] ShrinkRoleDirectory.occurrence BlockProgram.layout
  BlockSchedule.Templates.execute StateExecution.finalState executeLevels
set_option quotPrecheck false
local notation "pub" => terminalOperands G
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "rowBase" => endAddress D
local notation "rowEnd" => rowBase + words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "labelCount" => Fintype.card B.Entry

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

local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes
local notation "before" j => layerBase B.recordLimit rowBase tags j

/-- The operand record at every genuine shrinking row. Its source certificate
comes from the prefix actually executed by the compressor and the protected
memory window at this vertex. -/
def physicalSiteBank
    (fits : ∀ x : sites, ∀ m, canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) labelCount n rowEnd (before x.val.1.val) limit m)
    (x : sites) : CanonicalSite B x.occurrence.i x.occurrence.state x.occurrence.selection
      x.occurrence.site G.w n labelCount := by
  let o := x.occurrence
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame
    x.val.1 o.selected
  exact compiledSite B f hf o.i o.state o.selection o.site pub (pub 2) X.positions T x.val.1.val
    n rowEnd (before x.val.1.val) (before (x.val.1.val + 1)) limit (passes).length
    phy payload width (fits x)

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
