import OAI.Computability.VPVNP.PairVirtualRootBudget
import OAI.Computability.VPVNP.PairShrinkAdjacentRows
import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses
import OAI.Computability.VPVNP.PairShrinkCallCapacity

/-! # Physical row bounds for every selected virtual shrinking site

Each child lies in the occurrence's input layer and precedes its selected
output row. The argument area and reload frame are the ones reserved by
the terminal program for the complete chronological branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open Compression BurstRAM LiveProgram PairStages.Group.Auxiliary CompressorRecords DescriptorSpace
open NodeArguments.ChildScan TraversalRows TraversalRoles PortRefresh.ArgumentAddress

/-- Address and width bounds consumed by the native shrinking row handler. -/
structure RowBounds {a g : ℕ} (Z : State a g) (regions : LeafArena.Regions)
    (w n cap rowEnd endLayer older parent : ℕ) : Prop where
  wire : Z.maxWireWidth ≤ n
  frameRoom : NativeFrame.frameBase regions + 12 ≤ 2^w
  above : n ≤ NativeFrame.frameBase regions
  strideFit : cap + 2 < 2^w
  fit : endLayer < 2^w
  oldNodes : ∀ v, childNode Z older cap v < rowEnd
  parentFit : parent < rowEnd
  earlier : ∀ v, childNode Z older cap v < parent
  abovePointer : ∀ v, n < regions.arguments.base (childNode Z older cap v)

variable {k A : Type} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (ok : B.IsSolution f) (G : PairStages.Group) (n T : ℕ)
variable {lanes : ℕ} (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f ok T hT X).Choices)
variable (x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f ok T hT X z))
local notation "vs" => executeLevels B f ok T hT X z
local notation "tags" => selected B f ok T hT X z
local notation "layers" => selectedLayers B f ok T hT X z
local notation "layout" => BlockProgram.layout B (Fin.val (terminalOperands G 2)) X.positions T
local notation "firstRow" => endAddress layout
local notation "rowEnd" => firstRow + tagWords B.recordLimit tags
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n (rowEnd) (Fintype.card B.Entry)
local notation "older" => layerBase B.recordLimit firstRow tags (Fin.val (Sigma.fst (Subtype.val x)))
local notation "later" => layerBase B.recordLimit firstRow tags ((Fin.val (Sigma.fst (Subtype.val x)))+1)

/-- Instantiate the row bounds at the input and output of the recovered occurrence. -/
noncomputable abbrev OccurrenceRowBounds : Prop :=
  let o := x.occurrence
  RowBounds o.state area G.w n B.recordLimit (rowEnd)
    (layerBase B.recordLimit firstRow tags ((vs).length+1)) (older)
    ((later)+(B.recordLimit+2)*siteOrdinal o.nextState o.site)

private theorem of_packed (pack : VertexPacked G layout B.recordLimit tags
      ((B.execute f ok T hT X).finalState z).totalWidth)
    (stack : (TerminalLayout.privateRegions (slotDegree S) n (firstRow+words B.recordLimit layers)
      (Fintype.card B.Entry)).stackBase < 2^G.w) (wire : x.occurrence.state.maxWireWidth ≤ n) :
    OccurrenceRowBounds B f ok G n T hT X z x := by
  let o := x.occurrence
  let p := (vs)[x.val.1]
  have occ : p = TraversalRows.shrinkLevel B f ok o.i o.state o.selection p.selector := o.selected
  have rowsEq : tagWords B.recordLimit tags = words B.recordLimit layers :=
    congrArg (words B.recordLimit) (selected_layers B f ok T hT X z)
  have stackFit : (area).stackBase < 2^G.w := by rw [rowsEq]; exact stack
  have rowsFit : rowEnd < 2^G.w :=
    (show rowEnd ≤ firstRow + 2*tagWords B.recordLimit tags +
      ((B.execute f ok T hT X).finalState z).totalWidth by omega).trans_lt (pack.arena.trans_lt (vertexHeader G).isLt)
  have one : 1 ≤ ((layers).map Layer.count).sum := by
    rw [selected_layer_counts B f ok T hT X z,List.sum_cons]
    exact (Nat.succ_le_of_lt X.positions_pos).trans (Nat.le_add_right ..)
  have stride : B.recordLimit+2 ≤ tagWords B.recordLimit tags := by
    rw [rowsEq, words]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (B.recordLimit+2) one
  have tagLength : (tags).length = (vs).length+1 := by simp [selected]
  have frame : NativeFrame.frameBase area ≤ (area).cacheBase := (area).hist_before
  have cache : (area).cacheBase+12 ≤ (area).stackBase := Nat.add_le_add_left (by decide : 12 ≤ 38) _
  refine ⟨wire, ((Nat.add_le_add_right frame 12).trans cache).trans stackFit.le, ?_,
    (stride.trans (Nat.le_add_left ..)).trans_lt rowsFit, ?_, ?_, ?_, ?_, ?_⟩
  · change n ≤ (n + (rowEnd)*(2*slotDegree S*n+1)) + Fintype.card B.Entry
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  · rw [← tagLength,layerBase,List.take_length]; exact rowsFit
  · intro v
    rw [ShrinkOldHalves.Physical.childNode_eq, rowsEq]
    exact ShrinkPackedRows.packed_shrink_address B f ok T hT X z (terminalOperands G 2).val
      x.val.1 o.i o.state o.selection p.selector occ v
  · rw [rowsEq]
    exact ShrinkPackedRows.packed_parent_address B f ok T hT X z (terminalOperands G 2).val
      x.val.1 o.i o.state o.selection p.selector occ o.site
  · intro v
    rw [ShrinkOldHalves.Physical.childNode_eq]
    exact ShrinkPackedRows.packed_child_before_parent B f ok T hT X z (terminalOperands G 2).val
      x.val.1 o.i o.state o.selection p.selector occ v o.site
  · intro v
    apply TerminalLayout.geometryPointer_before_node layout
    rw [ShrinkOldHalves.Physical.childNode_eq]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

end PairSimulation.ShrinkRole

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open CursorNetwork CursorBounds DescriptorSpace Filter

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (D : FixedProgramDiagonal.Program)
variable (B : S.Templates) (u : PairExponents B.growthConstant)

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout CursorNetwork.cursorState

/-- One threshold works for all nominations, specializations and selected
shrinking sites in the virtual pair's actual chronological execution. -/
theorem eventually_virtualShrinkRowBounds (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2^(D.geometry n).w) (clock : 44 ≤ n^10000)
      (A : Type) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
      let T := blockCount (u.θ : ℝ) n
      let X := V.scanState
      ∀ (z : (B.execute f ok T le_rfl X).Choices)
        (x : ShrinkRoleDirectory.ShrinkSite (executeLevels B f ok T le_rfl X z)),
        ShrinkRole.OccurrenceRowBounds B f ok (D.executionGroup n ht clock) n T le_rfl X z x := by
  filter_upwards [D.eventually_selectedRootBudget B u haddr hnum hden D.constants.circuitExponent,
    ShrinkCallCapacity.eventually_levels B u D.addressFactor haddr 1] with n budget limits
  intro hn V ht clock A _ f ok
  have raw := budget hn V ht clock A f ok
  dsimp only at raw ⊢
  rw [V.scanState_pairInput] at raw ⊢
  intro z x
  obtain ⟨pack,_,stack⟩ := raw.2.2.2 z
  apply ShrinkRole.of_packed _ _ _ _ _ _ _ _ _ _ pack stack
  let passes := executeLevels B f ok _ le_rfl _ z
  have width := (limits (laneLabels _ _ V.lanes) V.dimension le_rfl A f ok z
    (passes[x.val.1]) (List.getElem_mem x.val.1.isLt)).2
  rw [x.occurrence.selected, Nat.one_mul] at width
  exact (Nat.le_succ _).trans width

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
