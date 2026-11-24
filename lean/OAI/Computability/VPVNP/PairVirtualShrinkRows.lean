import OAI.Computability.VPVNP.PairSelectedShrinkRows
import OAI.Computability.VPVNP.PairVirtualShrinkPhysics
import OAI.Computability.VPVNP.PairVirtualShrinkLevelChecks
import OAI.Computability.VPVNP.PairVirtualShrinkSiteData
import OAI.Computability.VPVNP.PairVirtualPhysicalMapData
import OAI.Computability.VPVNP.PairVertexShrinkAtSite
import OAI.Computability.VPVNP.PairVirtualRootBudget

/-! # Native shrinking rows of the selected virtual pair

The chronological shrinking occurrences determine one bank of physical
readers. Each reader obtains its own selected terms, child directory and
map rows from the actual stored history. The same bank accounts for every
accepted path's monomial and every possible rejecting nomination tape,
including calls made after earlier counter flushes.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation
open Compression CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter
open TraversalRows TraversalRoles VertexImage LocalHistory NodeArguments TreeDecode
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant) {labels : ℕ}
    (order : B.Entry ≃ Fin labels)

attribute [local irreducible] VertexImage.placement VertexImage.template BlockProgram.layout
  BlockSchedule.Templates.execute CursorNetwork.cursorState selectedDesc ordinalJobCost
  ShrinkRoleDirectory.occurrence ShrinkRole.physicalSiteBank StateExecution.finalState executeLevels

set_option maxHeartbeats 1200000 in
-- The selected sites carry dependent parser and native program types indexed by the full branch.
/-- The selected shrinking reader is native on every active chronological
row, uniformly in the ring, compression solution and complete branch. -/
theorem eventually_virtualShrinkChecks_of_public (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000)
      (A : Type) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let ops := terminalOperands G
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f ok T le_rfl X
      let L := BlockProgram.layout B (ops 2).val X.positions T
      ∀ (z : E.Choices) {baseBits laneBits ord : ℕ} {tab : Fin L.shape.tables}
        {calendar reference m : Memory G.w} {bits : Fin (E.finalState z).totalWidth → Bool},
        (ops 6).val = n → (ops 9).val = labels →
        TerminalProgram.VertexEntry B f ok T le_rfl X z L tab baseBits laneBits ops
          calendar reference bits →
        SelectedPayloadHistory.Past B f ok L
          (CompiledResident.payload B f ok (ops 2) X.positions T n)
          (executeLevels B f ok T le_rfl X z) calendar →
        LinkedVertexMemory G reference ord m →
        TerminalProgram.ShrinkRows B f ok G n D.numerator D.denominator order T le_rfl X z m := by
  classical
  have lab : labels = Fintype.card B.Entry :=
    (Fintype.card_fin labels).symm.trans (Fintype.card_congr order.symm)
  subst labels
  filter_upwards [eventually_virtualShrinkCapacity D B u haddr hnum hden,
    eventually_virtualShrinkRowCost D B u order haddr D.constants.circuitExponent,
    eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    MapConstants.eventually_width B.shrink D.addressFactor D.address_pos] with
    n capacities costs roots word
  intro hn V ht clock A _ f ok G ops X T E L z baseBits laneBits ord tab calendar reference m bits
    length count entry history frame
  let passes := executeLevels B f ok T le_rfl X z
  let tags := TraversalRoles.selected B f ok T le_rfl X z
  let base := endAddress L
  let rows := selectedLayers B f ok T le_rfl X z
  let rowEnd := base + words B.recordLimit rows
  let region := TerminalLayout.privateRegions (slotDegree S) n rowEnd (Fintype.card B.Entry)
  let limit := ShrinkCallABI.hiddenBase region n +
    ShrinkCallCapacity.extent (X.positions * slotDegree S) n
  let before (j : ℕ) := layerBase B.recordLimit base tags j
  let host := (VertexImage.template (TerminalProgram.nativeSegments B D.constants D.numerator
    D.denominator order)).instantiate G.w ops
  have eqn : tagWords B.recordLimit tags = words B.recordLimit rows :=
    congrArg (words B.recordLimit) (selected_layers B f ok T le_rfl X z)
  obtain ⟨_, _, _, room⟩ := roots hn V ht clock A f ok
  obtain ⟨pack, _, stack⟩ := room z
  have budget := costs hn V A f ok z
  have width : MapConstants.widthThreshold B.shrink ≤ G.w := word
  have capacity := capacities hn V ht clock A f ok z
  have fits (x : ShrinkRoleDirectory.ShrinkSite passes) (j : x.occurrence.state.packingData.Motif) :
      ShrinkRole.canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection
        (w := G.w) (Fintype.card B.Entry) n rowEnd (before x.val.1.val) limit j := by
    have got := (capacity x).maps.fit j
    change ShrinkRole.canonicalFits B x.occurrence.i x.occurrence.state x.occurrence.selection
      (w := G.w) (Fintype.card B.Entry) n (base + tagWords B.recordLimit tags) (before x.val.1.val)
      (ShrinkCallABI.hiddenBase (TerminalLayout.privateRegions (slotDegree S) n
        (base + tagWords B.recordLimit tags) (Fintype.card B.Entry)) n +
        ShrinkCallCapacity.extent (X.positions * slotDegree S) n) j at got
    rw [eqn] at got
    exact got
  let bank := ShrinkRole.physicalSiteBank B f ok le_rfl X z history entry pack frame width fits
  have info (x : ShrinkRoleDirectory.ShrinkSite passes) :
      ShrinkRole.CanonicalSiteData (bank x) host f ok T le_rfl X z x.val.1
        (RoleDomains.siteId B f ok T le_rfl X z x) base := by
    exact VirtualShrink.Capacity.siteData (G := G) (n := n) (T := T) (limit := limit) (phy := m)
      B f ok le_rfl X z history entry pack frame width fits x
      host rfl (capacity x)
  have maps (x : ShrinkRoleDirectory.ShrinkSite passes)
      (parent : x.occurrence.nextState.network.Half x.occurrence.site) :
      ShrinkRole.CanonicalMapData (bank x) (vertexHeader G) parent :=
    ShrinkRole.physicalSiteMapData_virtual (G := G) (n := n) (T := T) (phy := m)
      B f ok le_rfl X z history entry pack frame width fits x
      (capacity x).maps parent
  have stackFit : (TerminalLayout.privateRegions (slotDegree S) n
      (base + tagWords B.recordLimit tags) (Fintype.card B.Entry)).stackBase ≤ 2 ^ G.w := by
    rw [eqn]
    exact stack.le
  have phy := PairSimulation.VirtualShrink.physics B f ok G n order T le_rfl X z m
    budget pack entry frame stackFit
  refine ⟨fun x => ShrinkRole.canonicalParent (bank x) order f ok, fun vals => ?_⟩
  let hist := privateHistogram (W := G.w) (endAddr := n) order.symm
    (TerminalLayout.privateRegions (slotDegree S) n (base + tagWords B.recordLimit tags)
      (Fintype.card B.Entry)).histBase
  have native := RoleDomains.nativeShrink_at_vertex (G := G) (n := n) (T := T) (limit := limit)
    (phy := m) (vals := vals) (counts := hist) (nodeCap := n ^ 9000)
    (wordLimit := n * n ^ 9000) B f ok le_rfl X z history entry pack frame width fits
    D.numerator D.denominator order length count info maps
  refine ⟨native, ?_⟩
  intro leaf refresh i isShrink
  exact PairSimulation.VirtualShrink.levelChecks_at (limit := limit) B f ok G n
    D.numerator D.denominator order T le_rfl X z m history entry pack frame width fits
    phy info maps vals native leaf refresh i isShrink

/-- Every linked vertex call of a sufficiently large virtual pair uses the
same native shrinking reader for both its path multiplicities and its resource
checks, for all scalar assignments and selected branches at that length. -/
theorem eventually_virtualShrinkChecks (hlabels : D.constants.motifLabels = Fintype.card B.Entry)
    (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000)
      (A : Type) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let ops := terminalOperands G
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f ok T le_rfl X
      let L := BlockProgram.layout B (ops 2).val X.positions T
      ∀ (z : E.Choices) {baseBits laneBits ord : ℕ} {tab : Fin L.shape.tables}
        {calendar reference m : Memory G.w} {bits : Fin (E.finalState z).totalWidth → Bool},
        TerminalProgram.VertexEntry B f ok T le_rfl X z L tab baseBits laneBits ops
          calendar reference bits →
        SelectedPayloadHistory.Past B f ok L
          (CompiledResident.payload B f ok (ops 2) X.positions T n)
          (executeLevels B f ok T le_rfl X z) calendar →
        LinkedVertexMemory G reference ord m →
        TerminalProgram.ShrinkRows B f ok G n D.numerator D.denominator order T le_rfl X z m := by
  classical
  have lab : D.constants.motifLabels = labels :=
    hlabels.trans ((Fintype.card_congr order).trans (Fintype.card_fin labels))
  filter_upwards [eventually_virtualShrinkChecks_of_public D B u order haddr hnum hden,
    D.eventually_terminalOperandSizes lab] with n checks sizes
  intro hn V ht clock A _ f ok G ops X T E L z b l j tab calendar reference m bits
    entry history frame
  have operandSizes := sizes ht clock
  exact checks hn V ht clock A f ok z operandSizes.1 operandSizes.2 entry history frame

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
