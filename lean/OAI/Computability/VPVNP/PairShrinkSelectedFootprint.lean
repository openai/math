import OAI.Computability.VPVNP.PairSelectedPacketGeometry
import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkRoleMapStartReads
import OAI.Computability.VPVNP.PairShrinkCanonicalFootprint
import OAI.Computability.VPVNP.PairShrinkSiteLocatorFootprint
import OAI.Computability.VPVNP.PairShrinkSiteStartFootprint
import OAI.Computability.VPVNP.PairShrinkSitePhysical

/-!
# External reads at a selected shrinking vertex

The physical site selects its map header, owner count, term descriptor and
interval banks from the chronological compressor payload. Their addresses
lie below the terminal controller in the same memory used by the vertex.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open scoped Fin.CommRing

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

variable (fits : ∀ x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z),
  ∀ m, canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection (w := G.w)
    (Fintype.card B.Entry) n
    (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T) +
      words B.recordLimit (selectedLayers B f hf T hT X z))
    (layerBase B.recordLimit
      (endAddress (BlockProgram.layout B (terminalOperands G 2).val X.positions T))
      (TraversalRoles.selected B f hf T hT X z) x.val.1.val) limit m)
variable (x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z))
local notation "atSite" => physicalSiteBank B f hf hT X z history entry packed frame width fits x
local notation "occ" => x.occurrence
local notation "owner" => (MapResidentRows.siteIndex (occ).state (occ).site).val
local notation "hdr" => vertexHeader G

/-- The published map headers and all their resident rows lie inside the
producing level, strictly below the terminal control cells. -/
theorem physicalSiteBank_mapArea :
    (atSite).source.InLevel D x.val.1.val ∧ levelStart D (x.val.1.val + 1) ≤ (hdr).val := by
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame
    x.val.1 (occ).selected
  have below : endAddress D ≤ (hdr).val :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans packed.arena)
  refine ⟨?_, (levelStart_mono D payload.bounds.nextLive.le).trans below⟩
  exact compiledSite_inLevel B f hf (occ).i (occ).state (occ).selection (occ).site
    pub (pub 2) X.positions T x.val.1.val n rowEnd (before x.val.1.val) (before (x.val.1.val + 1))
    limit (passes).length phy payload width (fits x)

/-- The four header loads and the indirect load of the site's resident
count in the compiled reader preserve external memory. -/
theorem physicalSiteBank_mapStart_footprint (node : Word G.w) (saved : DFS.Scratch G.w n) :
    let load := ShrinkVertexImage.mapStartSetup phy (atSite).level (owner : Word G.w)
    let es := load.trace node saved
    SourceTransport.Reads (TerminalLink.workerCell hdr) es ∧
      SourceTransport.Writes (fun _ ↦ False) es := by
  dsimp only
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame
    x.val.1 (occ).selected
  have area := physicalSiteBank_mapArea B f hf hT X z history entry packed frame width fits x
  have heads := compiledSite_published B f hf (occ).i (occ).state (occ).selection (occ).site
    pub (pub 2) X.positions T x.val.1.val n rowEnd (before x.val.1.val) (before (x.val.1.val + 1))
    limit (passes).length phy payload width (fits x)
  have hroom := packed.room
  constructor
  · exact ShrinkVertexImage.mapStart_worker_reads B (occ).i (atSite).source (occ).site hdr
      (by omega) (area.1.headerEnd.le.trans area.2) (area.1.rowsEnd.trans area.2) heads
  · exact ShrinkVertexImage.mapStartSetup_noWrites phy (atSite).level (owner : Word G.w) node saved

local notation "leaf" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor

set_option maxHeartbeats 1800000 in
-- Identify the selected input and output sites throughout the packed source and parser.
/-- On any accepted tape the selected shrinking row returns its original
external memory. Every external read belongs to the live terminal worker. -/
theorem physicalSiteBank_trace (labelOrder : B.Entry → Fin labelCount) (node : Word G.w)
    (saved : DFS.Scratch G.w n) (bits : List Bool) (job : DFS.VisitPath G.w n) (tail : List Bool)
    (atRow : node.val = ShrinkRoleDirectory.address B.recordLimit rowBase leaf passes x.val)
    (hit : (canonicalParent (atSite) labelOrder f hf).read node saved bits = some (job, tail)) :
    after phy job.trace = phy ∧ SourceTransport.Reads (TerminalLink.workerCell hdr) job.trace := by
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame
    x.val.1 (occ).selected
  have area := physicalSiteBank_mapArea B f hf hT X z history entry packed frame width fits x
  have heads := compiledSite_published B f hf (occ).i (occ).state (occ).selection (occ).site
    pub (pub 2) X.positions T x.val.1.val n rowEnd (before x.val.1.val) (before (x.val.1.val + 1))
    limit (passes).length phy payload width (fits x)
  obtain ⟨_, sources⟩ := ShrinkSiteBank.rowSources_vertex B f hf hT X z X.positions n
    x.val.1 (occ).i (occ).state (occ).selection _ (occ).selected history entry packed frame
  have hroom := packed.room
  have beforeHeader : endAddress D ≤ (hdr).val :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans packed.arena)
  have result := canonicalParent_worker (atSite) labelOrder f hf hdr node saved bits job tail
    (by omega) beforeHeader rfl payload rfl area.1 area.2 heads
    (physicalSiteBank_locator_footprint B f hf hT X z history entry packed frame width fits
      x node saved)
    (fun out rest read ↦ physicalSiteBank_child_footprint B f hf hT X z history entry packed frame
      width fits x atRow read)
    (fun parent old q ↦ sources (occ).site old parent q) hit
  exact ⟨result.2, result.1⟩

/-- The actual row pointer in the selected traversal fits its word. At this
pointer every successful canonical read satisfies the external-memory laws. -/
theorem physicalSiteBank_rowTrace (labelOrder : B.Entry → Fin labelCount)
    (saved : DFS.Scratch G.w n) (bits : List Bool) (job : DFS.VisitPath G.w n) (tail : List Bool)
    (hit : (canonicalParent (atSite) labelOrder f hf).read
      (ShrinkRoleDirectory.address B.recordLimit rowBase leaf passes x.val : Word G.w) saved bits =
        some (job, tail)) :
    after phy job.trace = phy ∧ SourceTransport.Reads (TerminalLink.workerCell hdr) job.trace := by
  have tagEq : tagWords B.recordLimit tags = words B.recordLimit (selectedLayers B f hf T hT X z) :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have room := packed.arena
  have limit₀ : (hdr).val < 2 ^ G.w := (hdr).isLt
  have fit : layerBase B.recordLimit rowBase tags ((passes).length + 1) ≤ 2 ^ G.w := by
    rw [TreeDecode.selected_endBase, ← tagEq]
    omega
  have decoded := ShrinkRoleDirectory.decode_address B.recordLimit rowBase leaf passes fit x
  exact physicalSiteBank_trace B f hf hT X z history entry packed frame width fits x labelOrder
    _ saved bits job tail
    ((ShrinkRoleDirectory.decode_eq_some_iff B.recordLimit rowBase leaf passes fit _ x).mp decoded)
    hit

end PairSimulation.ShrinkRole

end

end VPVNP
end Computability
end OAI
