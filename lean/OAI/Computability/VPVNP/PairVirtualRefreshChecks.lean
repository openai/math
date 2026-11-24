import OAI.Computability.VPVNP.PairRefreshOriginLevel
import OAI.Computability.VPVNP.PairRefreshSelectedLevelMemory
import OAI.Computability.VPVNP.PairVertexRoleNativeRefresh
import OAI.Computability.VPVNP.PairVertexRatedRoles
import OAI.Computability.VPVNP.PairVirtualRefreshRoom
import OAI.Computability.VPVNP.PairSelectedRefreshRows
import OAI.Computability.VPVNP.PairVertexSelectedClock

/-! # The complete refresh role of the physical virtual-pair program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter LocalHistory
open TraversalRows TraversalRoles VertexImage TreeDecode
open private blocks_le_log from OAI.Computability.VPVNP.CompressorDirectoryBudget
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (D : FixedProgramDiagonal.Program)
  (B : S.Templates) (u : PairExponents B.growthConstant) {labels : ℕ} (order : B.Entry ≃ Fin labels)

attribute [local irreducible] VertexImage.placement VertexImage.template BlockProgram.layout
  BlockSchedule.Templates.execute RefreshHook.SelectedRows.parser CursorNetwork.cursorState
  CursorBounds.wordBits selectedDesc ordinalJobCost

set_option maxHeartbeats 1200000 in
-- The selected branch fixes the dependent argument state at every kernel visit.
set_option exponentiation.threshold 10000 in
/-- All selected refresh rows of the actual virtual pair share a length
threshold and the same installed reader, including in memories reached
after an arbitrary number of preceding vertex calls. -/
theorem eventually_virtualRefreshChecks (haddr : max S.laneBits 5 ≤ D.addressFactor)
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
        TerminalProgram.RefreshRows B f ok G n D.numerator D.denominator order T le_rfl X z m := by
  filter_upwards [eventually_virtualRefreshRooms D B u labels haddr hnum hden,
    eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    eventually_histogram_credit D.addressFactor D.address_pos,
    RefreshHook.SelectedRows.eventually_levelChecks B order D.constants
      D.numerator D.denominator]
    with n rooms roots credit checks
  intro hn V ht clock A _ f ok G ops X T E L z baseBits laneBits ord tab calendar reference m
    bits entry history frame
  let passes := executeLevels B f ok T le_rfl X z
  let leaf : TaggedLayer := ⟨leafLayer (siteOrder X), .cursor⟩
  let tags := selected B f ok T le_rfl X z
  let width := (E.finalState z).totalWidth
  let size := tagWords B.recordLimit tags
  let region := TerminalLayout.privateRegions (slotDegree S) n (endAddress L + size) labels
  let room := rooms hn V ht clock A f ok z
  let refresh := RefreshHook.SelectedRows.parser n labels G.w (ops 2).val X.positions T width leaf
    passes room order ops m
  let segments := TerminalProgram.nativeSegments B D.constants D.numerator D.denominator order
  let place := placement segments
  let host := (template segments).instantiate G.w ops
  obtain ⟨_, _, _, root⟩ := roots hn V ht clock A f ok
  obtain ⟨packed, _, stack⟩ := root z
  have rowsEq : size = words B.recordLimit (selectedLayers B f ok T le_rfl X z) :=
    congrArg (words B.recordLimit) (selected_layers B f ok T le_rfl X z)
  have labelsEq : labels = Fintype.card B.Entry :=
    (Fintype.card_fin labels).symm.trans (Fintype.card_congr order.symm)
  have fits : region.stackBase ≤ 2 ^ G.w := by
    change (TerminalLayout.privateRegions (slotDegree S) n
      (endAddress L + size) labels).stackBase ≤ _
    rw [rowsEq, labelsEq]
    exact stack.le
  have memory := RefreshHook.SelectedRows.levelMemory_at B f ok G n labels T le_rfl X z room
    entry history packed frame fits (blocks_le_log B u (by omega))
  refine ⟨refresh, fun vals => ?_⟩
  constructor
  · exact RoleDomains.nativeRefresh B f ok G (ops 2) X.positions T le_rfl X z
      entry history packed frame room
      D.numerator D.denominator order
  · intro old shr i tag
    have cap : n ≤ n ^ 9000 :=
      (Nat.pow_one n).symm.le.trans (Nat.pow_le_pow_right (by omega) (by decide))
    exact checks f ok T le_rfl X z G.w (ops 2).val X.positions width room place host m
      (template_contains segments ops) memory _ vals (n ^ 9000) (n * n ^ 9000) 1
      (RatedRoles.scan B order) cap credit le_rfl (RatedRoles.role_le B order .refresh)
      (RoleDomains.handlers old shr refresh) rfl i tag

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
