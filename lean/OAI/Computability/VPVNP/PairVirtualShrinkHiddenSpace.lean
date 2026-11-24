import OAI.Computability.VPVNP.PairVirtualRootBudget
import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairShrinkPackedCapacity
import OAI.Computability.VPVNP.PairShrinkPreparedCall
import OAI.Computability.VPVNP.PairShrinkCallABI

/-! # Private hidden-field capacity at a decoded shrinking site of the virtual pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open DescriptorSpace CursorBounds CursorNetwork Filter LocalHistory TraversalRows TraversalRoles
open ShrinkRoleDirectory ShrinkCallCapacity Compression.ShrinkMotif

variable {K : Type} [_root_.Field K] {S : BlockSchedule K}
    (D : FixedProgramDiagonal.Program) (B : S.Templates) (u : PairExponents B.growthConstant)

namespace VirtualShrink

variable {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
    {passes : List (SelectedLevel B f hf)} (x : ShrinkSite passes)
local notation "o" => ShrinkSite.occurrence x

open Classical in
/-- Each hidden field fits one square slot, and the slots for all hidden identifiers
of the selected input fit in the private region following the leaf stacks. -/
structure HiddenSpace (n w rowEnd : ℕ) : Prop where
  width : ∀ motif t, ShrinkPreparedCall.width B.shrink (o).state (o).selection motif
    (!ShrinkSlots.selectedLayout (o).state B.shrink (o).selection, t) ≤ n ^ 2
  capacity : ShrinkCallABI.hiddenBase
    (TerminalLayout.privateRegions (slotDegree S) n rowEnd (Fintype.card B.Entry)) n +
      (ShrinkHistoryRows.hiddenOrder (o).state).length * n ^ 2 ≤ 2 ^ w

end VirtualShrink

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState

set_option maxHeartbeats 1500000 in
-- The selected pass carries the dependent state, motif and directory indices.
/-- A single length threshold covers all shrinking occurrences of all virtual scans,
using the row end of the actual selected branch. -/
theorem eventually_virtualShrinkHiddenSpace (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000)
      (A : Type) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let L := BlockProgram.layout B (terminalOperands G 2).val X.positions T
      ∀ (z : (B.execute f hf T le_rfl X).Choices)
        (x : ShrinkSite (executeLevels B f hf T le_rfl X z)),
        VirtualShrink.HiddenSpace B x n G.w (endAddress L +
          tagWords B.recordLimit (selected B f hf T le_rfl X z)) := by
  classical
  let start n := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
  have poly : PolynomiallyBounded start := by
    have eqn : start = fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval
        (paperGeometry D.addressFactor (liveCapacity u) n) := by
      funext n
      exact congrArg (PublicExpr.eval · (LiveProgram.Layout.pairWorkspace D.constants))
        (paperGeometry_eq D B u hnum hden n)
    rw [eqn]
    exact CompressedPair.startup_workspace_polynomial _ D.address_pos (liveCapacity_polynomial u)
  filter_upwards [eventually_packed_handoff B u D.addressFactor haddr poly,
    eventually_levels B u D.addressFactor haddr (fieldFactor B.shrink),
    CompressedPair.eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u)]
    with n handoff levels inputs
  intro hn V ht clock A _ f hf G X T L
  dsimp only [L, X]
  rw [V.scanState_pairInput]
  let labels := laneLabels _ _ V.lanes
  let initial := pairInput S labels V.dimension
  let P := initialPositions D.addressFactor n
  have pos : initial.positions = P := pairInput_positions S labels V.dimension
  have ports := inputs (CounterPublic.actualPrefix D.literal)
  rw [← paperGeometry_eq D B u hnum hden n] at ports
  have startEq : (terminalOperands G 2).val = start n := ports.1
  let firstRow := endAddress (BlockProgram.layout B (start n) P T)
  change ∀ (z : (B.execute f hf T le_rfl initial).Choices)
    (x : ShrinkSite (executeLevels B f hf T le_rfl initial z)), VirtualShrink.HiddenSpace B x n G.w
      (endAddress (BlockProgram.layout B (terminalOperands G 2).val initial.positions T) +
        tagWords B.recordLimit (selected B f hf T le_rfl initial z))
  rw [pos, startEq]
  intro z x
  let vs := executeLevels B f hf T le_rfl initial z
  let j := x.val.1
  let o := x.occurrence
  obtain ⟨positions, wide⟩ :=
    levels labels V.dimension le_rfl A f hf z vs[j] (List.getElem_mem j.isLt)
  change vs[j].input.positions ≤ P at positions
  change fieldFactor B.shrink * (vs[j].input.maxWireWidth + 1) ≤ n at wide
  have selectedAt : vs[j] =
      ShrinkRoleDirectory.shrinkLevel o.i o.state o.selection vs[j].selector :=
    o.selected
  rw [selectedAt] at positions wide
  have degree := vs[j].oldDegree_le
  rw [selectedAt] at degree
  have count := motif_count o.state positions degree
  constructor
  · intro motif t
    have field := o.state.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
      (Nat.two_pow_pos _) o.state.shrinkNumber o.state.packingWidth
      (fun _ => o.state.width_le_maxWireWidth _) B.shrink motif (o.selection motif)
    rw [pow_two]
    exact ((field.2 _).2.trans wide).trans (Nat.le_mul_of_pos_right _ (by omega))
  · let tags := selected B f hf T le_rfl initial z
    have sizes : tagWords B.recordLimit tags =
        words B.recordLimit (selectedLayers B f hf T le_rfl initial z) :=
      congrArg (words B.recordLimit) (selected_layers B f hf T le_rfl initial z)
    change ShrinkCallABI.hiddenBase (TerminalLayout.privateRegions (slotDegree S) n
      (firstRow + tagWords B.recordLimit tags) (Fintype.card B.Entry)) n +
        (ShrinkHistoryRows.hiddenOrder o.state).length * n ^ 2 ≤ 2 ^ (wordBits D.addressFactor n)
    rw [sizes]
    have bound := (handoff labels V.dimension le_rfl A f hf z).1
    have occupied : (ShrinkHistoryRows.hiddenOrder o.state).length * n ^ 2 ≤
        4 * (P * slotDegree S) * n ^ 2 := by
      change (ShrinkTermInputs.motifCount o.state * 4) * n ^ 2 ≤ _
      rw [Nat.mul_comm (ShrinkTermInputs.motifCount o.state) 4]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 count)
    apply le_trans (Nat.add_le_add_left (occupied.trans ?_) _) bound.le
    change 4 * (P * slotDegree S) * n ^ 2 ≤ extent (P * slotDegree S) n
    unfold extent
    omega

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
