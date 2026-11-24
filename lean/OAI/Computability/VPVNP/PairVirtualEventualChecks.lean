import OAI.Computability.VPVNP.PairVirtualActiveChecks
import OAI.Computability.VPVNP.PairVirtualCursorLeafExact
import OAI.Computability.VPVNP.PairVirtualRefreshChecks
import OAI.Computability.VPVNP.PairVirtualShrinkRows

/-! # All selected virtual-pair vertex calls on the installed program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter LocalHistory
open TraversalRows TraversalRoles VertexImage CutSchedule ExponentTrace TreeDecode NetworkKernel

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant) {labels : ℕ}
    (order : B.Entry ≃ Fin labels)

attribute [local irreducible] VertexImage.placement VertexImage.template BlockProgram.layout
  BlockSchedule.Templates.execute CursorNetwork.cursorState CursorBounds.wordBits
  selectedDesc ordinalJobCost

set_option maxHeartbeats 1600000 in
-- The physical site, model and lane numbering identify the three dependent role domains.
/-- The length threshold precedes the auxiliary nomination, coefficient
realization, selected branch, shared wire values and current site. Every
worker reads the true retained parser records and executes the same table. -/
theorem eventually_activeChecks (hlabels : D.constants.motifLabels = Fintype.card B.Entry)
    (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      [NeZero (virtualBits D.addressFactor n)]
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clk : 44 ≤ n ^ 10000)
      {p : Nat.Primes} {model : LabelEvaluator.Model p (B.compressorDegree n)
        (B.compressorEquations hn D.constants.circuitExponent)}
      (scalar : D.ScalarData B hn model)
      (ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)) (i : D.groupIndices n),
      let G := D.executionGroup n ht clk
      let ops := terminalOperands G
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let l := reservedLanes B u n
      let b := virtualBits D.addressFactor n - l
      let L := BlockProgram.layout B (ops 2).val X.positions T
      let f := B.compressorValues hn model
      let ok := B.compressorValues_solution hn model
      ∀ (μ : PairStages.Group.Nominations.Nom G)
        (A : CanonicalScan scalar V ξ i (physicalNomination rfl μ))
        (z : (V.selection (M := model)).Choices)
        {initial : Memory G.w} {N : PairStages.Group.Indexed G Stage.nominations initial
          (PairStages.Group.Nominations.Nom G)}
        (prepared : PreparedBranch G initial (physicalPairIndex i)
          ((physicalPairLengths (ht := ht) (hf := clk) i).symm ▸
            PairedChain.headers scalar.advice ξ i) N μ)
        {calendar reference m : Memory G.w} {tab : Fin L.shape.tables}
        {bits : Fin ((V.selection (M := model)).finalState z).totalWidth → Bool} {ord : ℕ},
        TerminalProgram.VertexEntry B f ok T le_rfl X z L tab b l ops calendar reference bits →
        SelectedPayloadHistory.Past B f ok L
          (CompiledResident.payload B f ok (ops 2) X.positions T n)
          (executeLevels B f ok T le_rfl X z) calendar →
        LinkedVertexMemory G reference ord m →
        (∀ x < (ops 2).val, x ≠ (PairTag.address ops).val →
          calendar x = prepared.copy.memory () x) →
        V.SelectedRowsAt scalar.advice ξ i μ order f ok A.leafSites z m 1
          (RatedRoles.scan B order) := by
  filter_upwards [eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    eventually_virtualCursorLeafExactCalls D B u order hlabels haddr hnum hden,
    eventually_virtualRefreshChecks D B u order haddr hnum hden,
    eventually_virtualShrinkChecks D B u order hlabels haddr hnum hden]
    with n roots cursors refreshes shrinks
  intro hn V inst ht clk p model scalar ξ i G ops X T l b L f ok μ A z initial N prepared
    calendar reference m tab bits ord entry history later low
  have all := roots hn V ht clk model.algebra f ok
  let pack := (all.2.2.2 z).1
  have names : Fintype.card B.Entry = labels :=
    (Fintype.card_congr order).trans (Fintype.card_fin labels)
  have count := (physical_counter_end G pack.fit).2.2.trans (hlabels.trans names)
  obtain ⟨fit, exactLeaf, leaves⟩ := cursors hn V ht clk scalar ξ i μ A z m 1
    (RatedRoles.scan B order) (RatedRoles.role_le B order .leaf) prepared entry later low
  exact V.activeChecks scalar.advice ξ i μ order f ok A.leafSites z b l ord m pack entry later
    all.2.2.1 count (shrinks hn V ht clk model.algebra f ok z entry history later)
    (refreshes hn V ht clk model.algebra f ok z entry history later)
    ⟨V.cursorLeafParser scalar ξ i μ m fit, exactLeaf, leaves⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
