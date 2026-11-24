import OAI.Computability.VPVNP.PairShrinkPackedRows
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses
import OAI.Computability.VPVNP.PairShrinkRoleChildDescriptor
import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.PairTerminalSiteDirectories
import OAI.Computability.VPVNP.PairVertexCompiledPayload
import OAI.Computability.VPVNP.PairShrinkRolePackedRow
import OAI.Computability.VPVNP.PairShrinkRolePackedNumeric

/-!
# The child directory of a packed shrinking visit

The producing level publishes seven child operands. The selected traversal
writes the children in placement-fiber order. Together these give the row
descriptor and its actual readback at a later physical vertex call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.PackedChildren

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs NodeArguments NodeArguments.ChildScan
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TerminalProgram
open scoped Fin.CommRing
set_option quotPrecheck false

/-- The published count of old incidences is the count in the input-state incidence model. -/
private theorem old_count {a g : ℕ} (Z : State a (packingLaneBits a g)) :
    DemandRAM.oldCount Z = Z.positions * 2 ^ a := by
  rw [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv _), Fintype.card_fin]

private theorem payload_width {a g : ℕ} (Z : State a g) (v : Z.network.Site) :
    ChildArguments.width Z v ≤ 2 * (2 ^ a) * Z.maxWireWidth := by
  let zero : Z.network.Half v := ⟨fun _ _ _ => false, fun _ _ _ => false⟩
  have size := Child.payload_length Z (Child.ofHalf Z v zero)
  rw [Child.payload_ofHalf] at size
  exact size.symm.trans_le (packed_length_le Z v zero)

/-- The child-stage premises needed by the physical site reader. -/
structure Ready {w a g : ℕ} (Z : State a g) (regions : LeafArena.Regions)
    (inc : IncidenceDirectory w) (m : Memory w) (older cap n addr : ℕ) (level : Word w)
    (desc : Word w → ChildArguments.Descriptor w Z) : Prop where
  columns : inc.ActualColumns Z m
  strideFit : cap + 2 < 2 ^ w
  above : n ≤ NativeFrame.frameBase regions
  frameRoom : NativeFrame.frameBase regions + 12 ≤ 2 ^ w
  headRoom : level.val + 38 < 2 ^ w
  directory : ∀ node : Word w, node.val = addr →
    (desc node).directoryBase = level + 14 ∧
    ChildArguments.Resident regions.arguments inc m older cap n node (desc node)
  bounds : ∀ node : Word w, node.val = addr → ∀ u ∈ (desc node).sites,
    childNode Z older cap u < regions.nodes ∧ n < regions.arguments.base (childNode Z older cap u)

variable {K R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "rows" => selectedLayers B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

variable {G : Group} {n : ℕ} (cur : Fin (executeLevels B f hf T hT X z).length)
variable (i : Fin S.steps) {g : ℕ}
variable (Z : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (sel : SelectedScore.Selection B Z) (tape : List Bool)
variable (occurrence : (executeLevels B f hf T hT X z)[cur] = shrinkLevel B f hf i Z sel tape)

local notation "pub" => terminalOperands G
local notation "L" => BlockProgram.layout B (terminalOperands G 2).val X.positions T
local notation "firstRow" => endAddress L
local notation "rowEnd" => firstRow + words B.recordLimit rows
local notation "old" => layerBase B.recordLimit firstRow tags cur.val
local notation "later" => layerBase B.recordLimit firstRow tags (cur.val + 1)
local notation "inc" => packedIncidence L G.w cur.val (Z.positions * 2 ^ ShrinkBlockInputs.a i)
local notation "area" =>
  TerminalLayout.privateRegions (slotDegree S) n (rowEnd) (Fintype.card B.Entry)

variable {baseBits laneBits ord : ℕ}
variable {table : Fin (BlockProgram.layout B (terminalOperands G 2).val X.positions T).shape.tables}
variable {calendar reference phy : Memory G.w}
variable {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool}
variable (entry : VertexEntry B f hf T hT X z
  (BlockProgram.layout B (terminalOperands G 2).val X.positions T) table baseBits laneBits
  (terminalOperands G) calendar reference bits)
variable (pack : VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val X.positions T)
  B.recordLimit (selected B f hf T hT X z)
  (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
variable (frame : LinkedVertexMemory G reference ord phy)

include occurrence in
/-- The private child argument interval is strictly above the geometry pointer
and ends below the histogram for every input site, including all members of
the selected fiber. -/
theorem child_geometry (maxWidth : Z.maxWireWidth ≤ n)
    (frameRoom : NativeFrame.frameBase area + 12 ≤ 2 ^ G.w) (u : Z.network.Site) :
    let child := childNode Z old B.recordLimit u
    child < (area).nodes ∧ n < (area).arguments.base child ∧
      ChildArguments.width Z u ≤ (area).arguments.stride ∧
      (area).arguments.base child + ChildArguments.width Z u < 2 ^ G.w := by
  intro child
  have below : child < rowEnd := by
    rw [show child = _ from ShrinkOldHalves.Physical.childNode_eq Z old B.recordLimit u]
    exact ShrinkPackedRows.packed_shrink_address B f hf T hT X z (pub 2).val cur i Z sel tape
      occurrence u
  have low : firstRow ≤ child := by
    change firstRow ≤ firstRow + _ + _
    omega
  have degree : 2 ^ ShrinkBlockInputs.a i ≤ slotDegree S :=
    (shrinkLevel B f hf i Z sel tape).oldDegree_le
  have len : ChildArguments.width Z u ≤ (area).arguments.stride :=
    (payload_width Z u).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 degree) maxWidth).trans
      (Nat.le_succ _))
  have hist : (area).histBase < 2 ^ G.w := by
    unfold NativeFrame.frameBase at frameRoom
    omega
  exact ⟨below, TerminalLayout.geometryPointer_before_node L low, len,
    ((Nat.add_le_add_left len _).trans ((area).node_before below)).trans_lt hist⟩

include pack in
/-- The stride and exclusive end fit the actual machine word, including the
first nonempty cursor layer. -/
theorem row_fit :
    B.recordLimit + 2 < 2 ^ G.w ∧ layerBase B.recordLimit firstRow tags ((passes).length + 1) <
      2 ^ G.w := by
  have packedRoom := pack.arena
  have endEq : tagWords B.recordLimit tags = words B.recordLimit rows :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  rw [endEq] at packedRoom
  have room : rowEnd < 2 ^ G.w := calc
    _ ≤ firstRow + 2 * words B.recordLimit rows + (Y).totalWidth := by omega
    _ ≤ (vertexHeader G).val := packedRoom
    _ < _ := (vertexHeader G).isLt
  have positive : 1 ≤ ((rows).map Layer.count).sum := by
    rw [selected_layer_counts B f hf T hT X z, List.sum_cons]
    exact (Nat.succ_le_of_lt X.positions_pos).trans (Nat.le_add_right _ _)
  have stride := Nat.mul_le_mul_left (B.recordLimit + 2) positive
  rw [Nat.mul_one] at stride
  have count : (tags).length = (passes).length + 1 := by simp [selected]
  rw [← count, layerBase, List.take_length, selected_layers]
  exact ⟨(stride.trans (Nat.le_add_left _ _)).trans_lt room, room⟩

local notation "level" => levelHead pub phy cur.val

set_option maxHeartbeats 1500000 in
-- The native memory predicates have dependent types indexed by the chosen compression term.
include occurrence entry pack frame in
/-- At the real packed vertex call, the retained source supplies the incidence
columns and seven directory operands. The stored traversal supplies the popped
row and the exact ordered child words. The two numeric hypotheses hold
simultaneously for all occurrences by `eventually_geometry`. -/
theorem of_payload
    (data : CompiledResident.ShrinkPayload B (pub 2) X.positions T n cur.val i Z sel phy)
    (site : MapResidentRows.Site Z) (maxWidth : Z.maxWireWidth ≤ n)
    (frameRoom : NativeFrame.frameBase area + 12 ≤ 2 ^ G.w) :
    let desc := descriptor level (oldSites B f hf i Z sel site)
    let target := address B.recordLimit later (MapResidentRows.siteIndex Z site).val
    Ready Z area inc phy old B.recordLimit n target level desc := by
  intro desc target
  have live : (passes).length < (L).levels :=
    (executeLevels_length B f hf T hT X z).trans_lt (by rw [BlockProgram.actual_level_count]; omega)
  obtain ⟨low, high⟩ := pack.traversal_frames frame
  have wide : 28 ≤ (L).shape.scalarFields := by change 28 ≤ 54; decide
  obtain ⟨ds, stored⟩ := entry.site_directories live wide low high
  have head := entry.site_level_head live wide low high cur.val cur.isLt.le
  have baseCell : phy (levelStart L cur.val + 14) = (old : Word G.w) := by
    have cell := stored.currentBase cur.val (by
      simpa only [levelFibers, List.length_ofFn] using cur.isLt.le)
    rw [levelFibers_tags passes ds] at cell
    simpa only [levelStart, Nat.zero_mul, Nat.add_zero, TraversalRoles.selected] using cell
  have operands : (ChildScan.directory (ShrinkBlockInputs.a i) old B.recordLimit
      (area).arguments inc).Stored phy (level + 14) := by
    rw [head.1]
    exact data.child.bank old baseCell
  have cols := data.sources.old.incidence
  rw [old_count Z] at cols
  have layers := selected_layers B f hf T hT X z
  have rowMem := pack.rows frame (layers ▸ selected_capacity B f hf T hT X z)
    (layers ▸ entry.rows)
  rw [layers] at rowMem
  have row := selectedChildRow B f hf T hT X z i Z sel tape cur occurrence rowMem site
  have caps := row_fit B f hf T hT X z pack
  have rowEndFit : rowEnd < 2 ^ G.w := by
    have count : (tags).length = (passes).length + 1 := by simp [selected]
    simpa only [← count, layerBase, List.take_length, layers] using caps.2
  have child := child_geometry B f hf T hT X z cur i Z sel tape occurrence maxWidth frameRoom
  have oldRoom : levelStart L cur.val + 65 < 2 ^ G.w := data.words.oldRoom
  have headRoom : (level).val + 38 < 2 ^ G.w := by rw [head.2]; omega
  have above : n ≤ (area).histBase := Nat.le_add_right _ _
  refine ⟨cols, caps.1, above.trans (Nat.le_add_right _ _), frameRoom, headRoom, ?_, ?_⟩
  · intro node addr
    refine ⟨rfl, operands, ?_, fun u _ => (child u).1.trans rowEndFit,
      fun u _ => (child u).2.1.le, fun u _ => (child u).2.2.1, fun u _ => (child u).2.2.2⟩
    change DFS.Row phy node.val (node.val + 2)
      ((oldSites B f hf i Z sel site).map fun u => (childNode Z old B.recordLimit u : Word G.w))
    rw [addr]
    exact row
  · exact fun _ _ u _ => ⟨(child u).1, (child u).2.1⟩

include occurrence entry pack frame in
/-- The packed child certificate is available at any later physical site,
directly from the calendar's retained payloads and the linked vertex frame. -/
theorem atVertex
    (history : SelectedPayloadHistory.Past B f hf L
      (CompiledResident.payload B f hf (pub 2) X.positions T n) passes calendar)
    (site : MapResidentRows.Site Z) (maxWidth : Z.maxWireWidth ≤ n)
    (frameRoom : NativeFrame.frameBase area + 12 ≤ 2 ^ G.w) :
    let desc := descriptor level (oldSites B f hf i Z sel site)
    let target := address B.recordLimit later (MapResidentRows.siteIndex Z site).val
    Ready Z area inc phy old B.recordLimit n target level desc := by
  have data := CompiledResident.shrink_vertex history entry pack frame cur occurrence
  exact of_payload B f hf T hT X z cur i Z sel tape occurrence entry pack frame data site
    maxWidth frameRoom

end PairSimulation.ShrinkRole.PackedChildren

end VPVNP
end Computability
end OAI
