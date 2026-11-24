import OAI.Computability.VPVNP.PairVirtualShrinkRowBounds
import OAI.Computability.VPVNP.PairVirtualShrinkHiddenSpace
import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairShrinkCanonicalWorkspaceFit
import OAI.Computability.VPVNP.PairShrinkRoleHiddenCapacity
import OAI.Computability.VPVNP.PairShrinkPackedPackets
import OAI.Computability.VPVNP.PairSimulationMapConstants

/-!
# Capacity of a physical shrinking site in the virtual pair

The popped row determines a chronological shrinking occurrence, its
selected terms and its packed output site. The word bound applies to the
actual terminal workspace, old and new row bases, and private map reserve.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open DescriptorSpace CursorBounds CursorNetwork Filter LocalHistory
open TraversalRows TraversalRoles ShrinkRoleDirectory
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (D : FixedProgramDiagonal.Program) (B : S.Templates) (u : PairExponents B.growthConstant)

namespace VirtualShrink

variable {A : Type*} [CommRing A] {f : B.Entry → A} {ok : B.IsSolution f}
  {passes : List (SelectedLevel B f ok)} (x : ShrinkSite passes)
  {w : ℕ} (workspace : Word w) (positions blocks n firstRow rowWords : ℕ) (tags : List TaggedLayer)
local notation "o" => ShrinkSite.occurrence x
local notation "cur" => Fin.val (Sigma.fst (Subtype.val x))
local notation "rowEnd" => firstRow + rowWords
local notation "area" =>
  TerminalLayout.privateRegions (slotDegree S) n (rowEnd) (Fintype.card B.Entry)
local notation "lim" =>
  ShrinkCallABI.hiddenBase area n + ShrinkCallCapacity.extent (positions * slotDegree S) n
local notation "oldBase" => layerBase B.recordLimit firstRow tags cur
local notation "newBase" => layerBase B.recordLimit firstRow tags (cur + 1)

open Classical in
/-- The actual map, hidden read and child packet capacities of a decoded
shrinking site. All three use the same private area and published rows. -/
structure MapsAt : Prop where
  fit : ∀ m : (o).state.packingData.Motif,
    ShrinkRole.canonicalFits B (o).i (o).state (o).selection (w := w)
      (Fintype.card B.Entry) n rowEnd oldBase lim m
  hidden : ∀ mem : Memory w, CompiledResident.ShrinkPayload B workspace positions blocks n cur
      (o).i (o).state (o).selection mem →
    ShrinkRole.PackedHidden.Facts B (o).i (o).state (o).selection workspace positions blocks
      cur n area (o).site mem
  packets : ∀ (m : (o).state.packingData.Motif) (party : Fin 6)
      (sp : ShrinkResidentSources.Bounds B (o).i (o).state workspace positions blocks cur)
      (old : ShrinkCallDemandCells.Old (o).state
        (ShrinkSlots.selectedLayout (o).state B.shrink (o).selection) m party)
      (parent : (o).nextState.network.Half ((o).state.packingData.shrinkPartySite
        (ShrinkSlots.selectedLayout (o).state B.shrink (o).selection) m party)),
    let J := ShrinkCanonicalJob.job B (o).i (o).state (S.shrink (o).i) (o).selection m party
      workspace positions blocks cur sp n rowEnd oldBase newBase old parent
    ShrinkCanonicalJob.PacketSpace B (o).i (o).state (o).selection m party J n lim
  width : MapConstants.widthThreshold B.shrink ≤ w

/-- The row length is the size of the actually selected tagged layers. -/
abbrev Maps := MapsAt B x workspace positions blocks n firstRow (tagWords B.recordLimit tags) tags

end VirtualShrink

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState ShrinkRoleDirectory.occurrence ShrinkCanonicalJob.job
  TraversalRoles.layerBase ShrinkCallCapacity.extent

set_option maxHeartbeats 1200000 in
-- The packet and hidden-row types depend on the state decoded at the selected site.
/-- A single threshold supplies the private map and packet bounds for all
coefficient specializations, executions and decoded shrinking rows of the
actual virtual scan. -/
theorem eventually_virtualShrinkMaps (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000) (A : Type) [CommRing A]
      (f : B.Entry → A) (ok : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let workspace := terminalOperands G 2
      let L := BlockProgram.layout B workspace.val X.positions T
      ∀ (z : (B.execute f ok T le_rfl X).Choices)
        (x : ShrinkSite (executeLevels B f ok T le_rfl X z)),
        VirtualShrink.Maps B x workspace X.positions T n (endAddress L)
          (selected B f ok T le_rfl X z) := by
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
  filter_upwards [ShrinkCallCapacity.eventually_packed_occurrence B u D.addressFactor haddr poly,
    ShrinkRole.PackedHidden.eventually_hidden B u D.addressFactor haddr poly,
    ShrinkCanonicalJob.eventually_packets B u D.addressFactor haddr poly,
    MapConstants.eventually_width B.shrink D.addressFactor D.address_pos,
    CompressedPair.eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u)]
    with n fits hidden packets width inputs
  intro hn V ht clock A _ f ok G X T workspace L
  dsimp only [L,X]
  rw [V.scanState_pairInput]
  let labels := laneLabels _ _ V.lanes
  let initial := pairInput S labels V.dimension
  let count := initialPositions D.addressFactor n
  have pos : initial.positions = count := pairInput_positions S labels V.dimension
  have portsRead := inputs (CounterPublic.actualPrefix D.literal)
  rw [← paperGeometry_eq D B u hnum hden n] at portsRead
  have startEq : workspace.val = start n := portsRead.1
  let firstRow := endAddress (BlockProgram.layout B (start n) count T)
  change ∀ (z : (B.execute f ok T le_rfl initial).Choices)
    (x : ShrinkSite (executeLevels B f ok T le_rfl initial z)),
    VirtualShrink.Maps B x workspace initial.positions T n
      (endAddress (BlockProgram.layout B workspace.val initial.positions T))
      (selected B f ok T le_rfl initial z)
  rw [pos, startEq]
  intro z x
  let tags := selected B f ok T le_rfl initial z
  let o := x.occurrence
  let j := x.val.1
  have occ := o.selected
  have sizes : tagWords B.recordLimit tags =
      words B.recordLimit (selectedLayers B f ok T le_rfl initial z) :=
    congrArg (words B.recordLimit) (selected_layers B f ok T le_rfl initial z)
  let layers := selectedLayers B f ok T le_rfl initial z
  let region := NativeFrame.regions (slotDegree S) n firstRow (words B.recordLimit layers)
    (Fintype.card B.Entry)
  let limit := ShrinkCallCapacity.mapBase region (Fintype.card LeafStartup.ScalarPort) n +
    ShrinkCallCapacity.extent (count * slotDegree S) n
  change VirtualShrink.MapsAt B x workspace count T n firstRow (tagWords B.recordLimit tags) tags
  apply (congrArg
    (fun size => VirtualShrink.MapsAt B x workspace count T n firstRow size tags) sizes).mpr
  refine ⟨?_, ?_, ?_, width⟩
  · intro m
    have cap := fits labels V.dimension le_rfl A f ok z j o.i o.state o.selection _ occ m
    have converted := ShrinkRole.canonicalFits_of_selected B o.i o.state o.selection
      (b := D.addressFactor) (n := n) (firstRow := firstRow)
      (rowWords := words B.recordLimit layers)
      (older := layerBase B.recordLimit firstRow tags j.val) (limit := limit) m cap
    exact converted
  · intro mem payload
    have cap := hidden labels V.dimension le_rfl A f ok z j o.i o.state o.selection _ occ
      workspace mem payload o.site
    exact cap
  · intro m party sp old parent
    have cap := packets labels V.dimension le_rfl A f ok z j o.i o.state o.selection _ occ m party
      workspace sp old parent startEq
    exact cap

namespace VirtualShrink

variable {A : Type} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (G : PairStages.Group) (n T : ℕ) {lanes : ℕ} (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f ok T hT X).Choices)
    (x : ShrinkSite (executeLevels B f ok T hT X z))

local notation "tags" => selected B f ok T hT X z
local notation "workspace" => terminalOperands G 2
local notation "lay" => BlockProgram.layout B (Fin.val workspace) X.positions T
local notation "rowEnd" => endAddress lay + tagWords B.recordLimit tags

/-- The maps, packets, hidden widths and row addresses of the same selected
site in the physical execution. -/
structure Capacity : Prop where
  maps : Maps B x workspace X.positions T n (endAddress lay) tags
  hiddenSpace : HiddenSpace B x n G.w (rowEnd)
  rows : ShrinkRole.OccurrenceRowBounds B f ok G n T hT X z x

end VirtualShrink

/-- The physical shrinking-site bounds hold at one threshold chosen before
the coefficient assignment, all term selections and the popped site. -/
theorem eventually_virtualShrinkCapacity (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000) (A : Type) [CommRing A]
      (f : B.Entry → A) (ok : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      ∀ (z : (B.execute f ok T le_rfl X).Choices)
        (x : ShrinkSite (executeLevels B f ok T le_rfl X z)),
        VirtualShrink.Capacity B f ok G n T le_rfl X z x := by
  filter_upwards [eventually_virtualShrinkMaps D B u haddr hnum hden,
    eventually_virtualShrinkHiddenSpace D B u haddr hnum hden,
    eventually_virtualShrinkRowBounds D B u haddr hnum hden] with n maps hidden rows
  intro hn V ht clock A _ f ok G X T z x
  exact ⟨maps hn V ht clock A f ok z x, hidden hn V ht clock A f ok z x,
    rows hn V ht clock A f ok z x⟩

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
