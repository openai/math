import OAI.Computability.VPVNP.PairShrinkPhysicalSiteBank
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalData
import OAI.Computability.VPVNP.PairShrinkRolePackedChildren
import OAI.Computability.VPVNP.PairShrinkSiteOrdinal
import OAI.Computability.VPVNP.PairShrinkPackedParent

/-!
# The published operands of a shrinking site at a physical vertex call

Each operand is identified in the chronological level selected by the popped
row. The child reader, hidden reader and resident maps use the same parent
ordinal and the same retained compressor memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory
open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows TraversalRoles
open NodeArguments NodeArguments.ChildScan TraversalControllerInputs ShrinkBlockInputs
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
local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "rowsEnd" => endAddress D + words B.recordLimit (selectedLayers B f hf T hT X z)
local notation "before" j => layerBase B.recordLimit (endAddress D) tags j
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n rowsEnd
  (Fintype.card B.Entry)

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
local notation "side" => SelectedFinish.chosen B (o).state (o).selection
local notation "widths" => ShrinkHiddenRows.widths (o).state B.shrink (o).selection
local notation "old" => before x.val.1.val
local notation "new" => before (x.val.1.val + 1)
local notation "target" => address B.recordLimit new
  (MapResidentRows.siteIndex (o).state (o).site).val

set_option maxHeartbeats 4000000 in
-- Align the site chosen by the actual term history with the shared physical operand bank.
/-- The complete site data, for the role image instantiated with the terminal
worker's public words and the packed bounds of its genuine branch. -/
theorem physicalSiteData {p r : ℕ} (M : Machine G.w p r 11) (publicWords : M.publicData = pub)
    (wire : (o).state.maxWireWidth ≤ n)
    (frameRoom : NativeFrame.frameBase regions + 12 ≤ 2 ^ G.w)
    (earlier : ∀ u, childNode (o).state old B.recordLimit u < target)
    (slots : ∀ m t, widths m (!side, t) ≤ n ^ 2)
    (space : ShrinkCallABI.hiddenBase regions n + (ShrinkHistoryRows.hiddenOrder (o).state).length *
      n ^ 2 ≤ 2 ^ G.w)
    (hidden : PackedHidden.Facts B (o).i (o).state (o).selection (pub 2) X.positions T
      x.val.1.val n regions (o).site phy) :
    CanonicalSiteData site M f hf T hT X z x.val.1 id (endAddress D) := by
  let j := x.val.1
  let h := levelStart D j.val
  have atPass := (o).selected
  have payload := CompiledResident.shrink_vertex (G := G) history entry packed frame j atPass
  have children := PackedChildren.of_payload B f hf T hT X z j (o).i (o).state
    (o).selection _ atPass entry packed frame payload (o).site wire frameRoom
  have everyChild := PackedChildren.child_geometry (G := G) B f hf T hT X z j (o).i
    (o).state (o).selection _ atPass wire frameRoom
  have parent := ShrinkPackedRows.packed_parent_address B f hf T hT X z (pub 2).val j (o).i
    (o).state (o).selection _ atPass (o).site
  have rowRoom := PackedChildren.row_fit B f hf T hT X z packed
  have live : (vs).length < (D).levels :=
    (executeLevels_length B f hf T hT X z).trans_lt (by rw [BlockProgram.actual_level_count]; omega)
  obtain ⟨low, high⟩ := packed.traversal_frames frame
  have wide : 28 ≤ (D).shape.scalarFields := by
    unfold BlockProgram.layout
    change 28 ≤ 54
    decide
  have head := entry.site_level_head live wide low high j.val j.isLt.le
  have numeral := shrinkSiteOrdinal_eq B (o).i (o).state (o).selection (o).site
  have idVal := VertexImage.RoleDomains.siteId_val B f hf T hT X z x
  have hv : (h : Word G.w).val = h := Nat.mod_eq_of_lt (by
    have bound := payload.words.oldRoom
    change h + 65 < 2 ^ G.w at bound
    omega)
  refine ⟨publicWords.symm, rfl, rfl, ?_, ?_, idVal.symm, x.property, (o).index, rowRoom.2,
    children.columns, children.strideFit, children.above, frameRoom, ?_, ?_,
    fun u => (everyChild u).2.1,
    fun u => (everyChild u).1, parent, ?_, wire, slots, space, hidden.selectors,
    hidden.rowStride, ?_, ?_, hidden.countFit, hidden.count, hidden.valid,
    hidden.scratch, hidden.pitch.trans (pow_two n).symm, hidden.owner, ?_, ?_, rfl⟩
  · rw [publicWords]
    exact head.1.symm
  · change new + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal (o).nextState
      (o).site = new + (B.recordLimit + 2) * (id).val
    rw [numeral, idVal]
  · intro node eqn
    change node.val = new + (B.recordLimit + 2) *
      PortRefresh.ArgumentAddress.siteOrdinal (o).nextState (o).site at eqn
    rw [numeral] at eqn
    have got := children.directory node eqn
    rw [head.1] at got
    exact got
  · intro _ _
    rfl
  · intro u
    change childNode (o).state old B.recordLimit u < new + (B.recordLimit + 2) *
      PortRefresh.ArgumentAddress.siteOrdinal (o).nextState (o).site
    rw [numeral]
    exact earlier u
  · change (h : Word G.w).val + 38 < 2 ^ G.w
    rw [hv]
    exact hidden.headRoom
  · change ShrinkHiddenGuess.Header.Published _ (h : Word G.w).val phy
    rw [hv]
    exact hidden.headers
  · exact compiledSite_published B f hf (o).i (o).state (o).selection (o).site pub (pub 2)
      X.positions T j.val n rowsEnd old new limit (vs).length phy payload width (fits x)
  · exact compiledSite_mapRoom B f hf (o).i (o).state (o).selection (o).site pub (pub 2)
      X.positions T j.val n rowsEnd old new limit (vs).length phy payload width (fits x)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
