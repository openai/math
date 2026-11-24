import OAI.Computability.VPVNP.PairShrinkSiteLocatorFootprint
import OAI.Computability.VPVNP.PairShrinkRoleChildReads
import OAI.Computability.VPVNP.PairRefreshVertexInputWrites
import OAI.Computability.VPVNP.PairTraversalScanDirectory

/-!
# External probes at the start of a physical shrinking visit

The selected old incidence bank and the packed parent row bound every external
child probe. The decoder writes its guessed fields in private memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles NodeArguments NodeArguments.ChildScan
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary
open scoped Fin.CommRing

attribute [local irreducible] ShrinkRoleDirectory.occurrence
set_option quotPrecheck false

private theorem child_noWrites {w n a g : ℕ} {Z : State a g} {A : Arena}
    {inc : IncidenceDirectory w} {m : Memory w} {older cap : ℕ}
    {desc : Word w → ChildArguments.Descriptor w Z} {node : Word w} {saved : DFS.Scratch w n}
    {bs tail : List Bool} {out : Outcome w n (List (Child Z))}
    (read : ChildArguments.reader A inc m older cap desc node saved bs = some (out, tail)) :
    SourceTransport.Writes (fun _ => False) out.trace := by
  obtain ⟨_, result, _⟩ := ChildArguments.reader_some A inc m older cap desc read
  rw [congrArg Outcome.trace result]
  exact fun p v h => (List.mem_append.mp h).elim (ChildHeader.events_noWrites m _ _ p v)
    (ChildScan.events_noWrites Z inc m _ _ p v)

private theorem directory_row_end {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
    {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f}
    (cap base : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf))
    (x : ShrinkRoleDirectory.Site passes) :
    ShrinkRoleDirectory.address cap base leaf passes x + 2 + cap ≤
      base + tagWords cap (leaf :: ShrinkRoleDirectory.outputTags passes) := by
  let row := ShrinkRoleDirectory.siteRows passes x
  let output := ShrinkRoleDirectory.outputTags passes
  let tags := leaf :: output
  let j : Fin tags.length := ⟨row.1.val + 1, Nat.succ_lt_succ row.1.isLt⟩
  let id : Fin tags[j].layer.count := row.2
  exact ChildArguments.selected_row_end base cap tags j id

variable {K A : Type} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
  {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
  (z : (B.execute f hf T hT X).Choices)

private theorem fiber_length (i : Fin S.steps) {g : ℕ}
    (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : Z.ShrinkSelection B.shrink) (tape : List Bool)
    (member : shrinkLevel B f hf i Z sel tape ∈ executeLevels B f hf T hT X z)
    (v : MapResidentRows.Site Z) :
    (oldSites B f hf i Z sel v).length ≤ B.recordLimit := by
  classical
  have cap := selected_fiber_capacity B f hf T hT X z (shrinkLevel B f hf i Z sel tape) member v
  let order := ((shrinkPassReaders B f hf i rfl Z).order sel).children v
  have count := Fintype.card_congr order.entries
  rw [Fintype.card_fin] at count
  simpa only [oldSites, List.length_ofFn] using count.trans_le cap

variable {G : Group} {n limit : ℕ}

local notation "pub" => terminalOperands G
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "rowBase" => endAddress D
local notation "rowEnd" => rowBase + words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "labelCount" => Fintype.card B.Entry
local notation "before" j => layerBase B.recordLimit rowBase tags j
local notation "leaf" => TaggedLayer.mk (leafLayer (siteOrder X)) .cursor
local notation "sites" => ShrinkRoleDirectory.ShrinkSite passes

variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
  {baseBits laneBits ord : ℕ} {calendar reference phy : Memory G.w}
  {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
  (history : SelectedPayloadHistory.Past B f hf
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    (CompiledResident.payload B f hf (terminalOperands G 2) X.positions T n)
    (executeLevels B f hf T hT X z) calendar)
  (entry : TerminalProgram.VertexEntry B f hf T hT X z
    (BlockProgram.layout B (terminalOperands G 2).val X.positions T) table baseBits laneBits
    (terminalOperands G) calendar reference bits)
  (packed : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
    B.recordLimit (TraversalRoles.selected B f hf T hT X z)
    (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
  (frame : LinkedVertexMemory G reference ord phy)
  (width : MapConstants.widthThreshold B.shrink ≤ G.w)

local notation "bank" => physicalSiteBank B f hf hT X z history entry packed frame width
local notation "area" s => TerminalLayout.privateRegions (slotDegree S) n
  (CanonicalSite.rowEnd s) labelCount

set_option maxHeartbeats 2000000 in
-- The chronological level and its selected shrink kernel share dependent state indices.
/-- Every successful child decode at the packed row of this occurrence reads worker cells
and leaves external memory untouched, for every scratch state and input tape. -/
theorem physicalSiteBank_child_footprint
    (fits : ∀ x : sites, ∀ m, canonicalFits B x.occurrence.i x.occurrence.state
      x.occurrence.selection (w := G.w) labelCount n rowEnd (before x.val.1.val) limit m)
    (x : sites) {node : Word G.w} {saved : DFS.Scratch G.w n}
    {bs tail : List Bool} {out : Outcome G.w n (List (Child x.occurrence.state))}
    (atRow : node.val = ShrinkRoleDirectory.address B.recordLimit rowBase leaf passes x.val)
    (read : ChildArguments.reader (area (bank fits x)).arguments (bank fits x).incidence
      (bank fits x).mem (bank fits x).older B.recordLimit (bank fits x).descriptor node saved bs =
        some (out, tail)) :
    SourceTransport.Reads (TerminalLink.workerCell (vertexHeader G)) out.trace ∧
      SourceTransport.Writes (fun _ => False) out.trace := by
  refine ⟨ChildArguments.worker_reads_of_below _ packed.room ?_, child_noWrites read⟩
  let o := x.occurrence
  let j := x.val.1
  have data := CompiledResident.shrink_vertex (G := G) history entry packed frame j o.selected
  have count : IncidenceDirectory.slotCount o.state =
      o.state.positions * 2 ^ ShrinkBlockInputs.a o.i := by
    rw [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv _),
      Fintype.card_fin]
  have inc : (bank fits x).incidence =
      packedIncidence D G.w j.val (IncidenceDirectory.slotCount o.state) := by
    rw [count]
    rfl
  have rep : (bank fits x).incidence.ActualColumns o.state (bank fits x).mem := by
    rw [inc]
    exact data.sources.old.incidence
  let level : Fin (D).levels := ⟨j.val, Nat.lt_of_succ_lt data.bounds.nextLive⟩
  have columns := ChildArguments.ColumnsBelow.packed (w := G.w) D level data.bounds.oldCapacity
  have arena := packed.arena
  have descriptorEnd := directory_row_end B.recordLimit rowBase leaf passes x.val
  change ShrinkRoleDirectory.address B.recordLimit rowBase leaf passes x.val + 2 + B.recordLimit ≤
    rowBase + tagWords B.recordLimit tags at descriptorEnd
  rw [← atRow] at descriptorEnd
  have lower : rowBase ≤ (vertexHeader G).val := by omega
  have old := ChildArguments.old_fields_below (w := G.w) D level (by change 21 ≤ 66; decide)
  have directory : ((bank fits x).descriptor node).directoryBase =
      ((levelStart D j.val + 14 : ℕ) : Word G.w) := by
    change (levelStart D j.val : Word G.w) + 14 = _
    rw [Nat.cast_add]
    rfl
  have member : (passes)[x.val.1] ∈ passes := List.getElem_mem x.val.1.isLt
  rw [o.selected] at member
  have len := fiber_length B f hf hT X z o.i o.state o.selection _ member o.site
  apply ChildArguments.reader_reads_below rep _ _ _ _ read
  · rw [inc]
    exact ⟨columns.incoming.trans lower, columns.widths.trans lower⟩
  · omega
  · rw [directory]
    exact old.trans_le lower
  · change node.val + 2 + (oldSites B f hf o.i o.state o.selection o.site).length ≤ _
    omega

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
