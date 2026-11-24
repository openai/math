import OAI.Computability.VPVNP.PairShrinkPhysicalMapData
import OAI.Computability.VPVNP.PairVirtualShrinkCapacity

/-!
# Virtual-pair packet capacities at the physical map bank

The virtual bounds number the DFS arena by its tagged layers. The physical
site bank counts the same rows in the selected execution. Identifying those
two row counts places each virtual packet bound at exactly the canonical
job of the physical vertex.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open FixedProgramDiagonal.Program

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices) {G : Group} {n : ℕ}

attribute [local irreducible] ShrinkRoleDirectory.occurrence BlockProgram.layout
  BlockSchedule.Templates.execute StateExecution.finalState executeLevels
set_option quotPrecheck false
local notation "pub" => terminalOperands G
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "rowEnd" => endAddress D + words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "before" j => layerBase B.recordLimit (endAddress D) tags j
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n rowEnd
  (Fintype.card B.Entry)
set_option quotPrecheck false in
local notation "lim" => ShrinkCallABI.hiddenBase area n + ShrinkCallCapacity.extent
  (X.positions * slotDegree S) n
local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes

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

set_option maxHeartbeats 1800000 in
-- Align the packed packet types at the chronological occurrence and the common terminal row end.
/-- The packet field of the virtual-pair bound supplies the complete physical
map-data contract for any parent assignment at this shrinking vertex. -/
theorem physicalSiteMapData_virtual
    (fits : ∀ x : sites, ∀ m, canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) (Fintype.card B.Entry) n rowEnd (before x.val.1.val) lim m)
    (x : sites)
    (numeric : VirtualShrink.Maps B x (pub 2) X.positions T n (endAddress D) tags)
    (parent : x.occurrence.nextState.network.Half x.occurrence.site) :
    CanonicalMapData
      (physicalSiteBank B f hf hT X z history entry packed frame width fits x) (vertexHeader G)
      parent := by
  refine physicalSiteMapData B f hf hT X z history entry packed frame width fits x ?_ parent
  intro m party bounds old localParent
  have rowEq : tagWords B.recordLimit tags = words B.recordLimit (selectedLayers B f hf T hT X z) :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have bound := numeric.packets m party bounds old localParent
  rw [rowEq] at bound
  exact bound

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
