import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkSitePhysical
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalData

/-!
# Published map operands at the physical shrinking site

The actual chronological occurrence determines the parser's row and both
layer bases. Its retained sources cover every resident map of the site.
The numeric packet bounds use exactly the same selected job, including the
transport of the old and parent half-wires to the map's resident party.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices) {G : Group} {n limit : ℕ}

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

/-- Every motif and party at the selected site has room for its canonical job's packets
at the published level addresses, for each old and successor half-wire input. -/
def PhysicalSitePackets (x : sites) : Prop :=
  ∀ (m : x.occurrence.state.packingData.Motif) (party : Fin 6)
    (bounds : ShrinkResidentSources.Bounds B x.occurrence.i x.occurrence.state (pub 2)
      X.positions T x.val.1.val)
    (old : ShrinkCallDemandCells.Old x.occurrence.state
      (ShrinkSlots.selectedLayout x.occurrence.state B.shrink x.occurrence.selection) m party)
    (parent : x.occurrence.nextState.network.Half (x.occurrence.state.packingData.shrinkPartySite
      (ShrinkSlots.selectedLayout x.occurrence.state B.shrink x.occurrence.selection) m party)),
    let J := ShrinkCanonicalJob.job B x.occurrence.i x.occurrence.state
      (S.shrink x.occurrence.i) x.occurrence.selection m party
      (pub 2) X.positions T x.val.1.val bounds n rowEnd (before x.val.1.val)
      (before (x.val.1.val + 1)) old parent
    ShrinkCanonicalJob.PacketSpace B x.occurrence.i x.occurrence.state x.occurrence.selection
      m party J n limit

set_option maxHeartbeats 1800000 in
-- Match the selected resident and both dependent half-wire indices in the concrete job.
/-- At every physical shrink site the selected old and successor rows and the
fitted canonical job give all three fields of the native map's operand contract. -/
theorem physicalSiteMapData
    (fits : ∀ x : sites, ∀ m, canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) (Fintype.card B.Entry) n rowEnd (before x.val.1.val)
      limit m)
    (x : sites)
    (packets : PhysicalSitePackets (G := G) (n := n) (limit := limit) B f hf hT X z x)
    (parent : (x.occurrence.state.shrinkNext B.shrink (S.shrink x.occurrence.i)
      x.occurrence.selection).network.Half x.occurrence.site) :
    CanonicalMapData (physicalSiteBank B f hf hT X z history entry packed frame width fits x)
      (vertexHeader G) parent := by
  let o := x.occurrence
  obtain ⟨bounds, sources⟩ := ShrinkSiteBank.rowSources_vertex (G := G) B f hf hT X z X.positions n
    x.val.1 o.i o.state o.selection _ o.selected history entry packed frame
  refine ⟨?_, fun old q ↦ sources o.site old parent q, ?_⟩
  · exact (Nat.lt_succ_self _).trans_le packed.room
  · intro old q
    exact packets q.1.1 q.1.2 bounds _ _

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
