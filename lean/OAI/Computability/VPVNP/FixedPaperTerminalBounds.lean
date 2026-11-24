import OAI.Computability.VPVNP.FixedPaperRatedTerminal
import OAI.Computability.VPVNP.PairVertexOrdinalLiveCosts

/-! # Uniformly closing the costs of the physical terminal

The fixed vertex scan rate and raw pass charge are chosen before the input
length. The prelude and all accepting vertex reports then fit the physical
group clock and bucket for every nominated pair and every finite model.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open LabelEvaluator CompressorRecords ScheduledTrace PairStages PairStages.Group PairStages.Group.CompressedPaths
open PairSimulation LocalCount
open scoped Fin.CommRing
set_option quotPrecheck false
attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs CompressedPair.components TerminalProgram.workers

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (u : PairExponents B.growthConstant)
  (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry) (E : UniversalMachine.Program)
  (addr : ℕ) (positive : 1 ≤ addr)
local notation "D" => paperProgram B u c labels E addr positive
local notation "script" => BlockProgram.script B

/-- The true native role calls, chosen shared-bit data and chronological
prefix readbacks at one length. The scalar ring and advice are the ones
supplied by the joint finite model for this nominated pair. -/
abbrev PaperRatedRows (raw scanRate n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn c.circuitExponent))
    (data : (D).ScalarData B hn M) (V : (D).VirtualPairs B u hn c.circuitExponent) [NeZero (virtualBits ((D).addressFactor) n)],
    let G := (D).executionGroup n ((D).tagsFit n) (dispatchClock hn)
    ∀ (W : Conditions G (2^G.g.d) G.g.H) (P : PairStageConditions G (2^G.g.d) G.g.H)
      (cut : 1+B.denseCount n c.circuitExponent*(D).counterWidth n ≤ n^c.deltaPower)
      (I : VirtualPairs.PhysicalInput data W P rfl labels cut)
      (A : CanonicalScan data V (VirtualPairs.exterior data W P rfl labels cut I)
        (VirtualPairs.modelIndex data W P rfl labels cut I) (physicalNomination rfl I.μ)),
      let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
      let rate := nativePassRate script raw * initialPositions addr n
      ∀ Y : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) c labels base
        (fuel G) rate (publicWords G) (I.branch.copy.memory ()),
        RatedBranchesAt B u c labels E addr positive data V W P cut I A raw scanRate Y

set_option maxHeartbeats 1200000 in
theorem eventually_paperTerminals_of_rated (raw scanRate : ℕ) (enough : max S.laneBits 5 ≤ addr)
    (rows : ∀ᶠ n : ℕ in atTop, PaperRatedRows B u c labels E addr positive raw scanRate n) :
    ∀ᶠ n : ℕ in atTop, PaperTerminals B u c labels E addr positive c.circuitExponent rfl raw n := by
  obtain ⟨hd,start⟩ := eventually_paperStartup.{0} B u c labels E addr positive ((le_max_left ..).trans enough)
  let site := VertexReportBudget.coefficient S.baseDegree (Fintype.card B.Entry) 6 scanRate 0 0
  have clocks := eventually_branchClocks.{0,0} B u addr enough (paperBootstrap B u) (script).initial.length
    (script).block.length raw site 1 0
  have preludeBounds := eventually_paperDescriptorPrelude (D) B u c.circuitExponent enough rfl rfl c labels
  have geometry := VertexImage.eventually_ordinal_geometry B u c (liveRatio u).num (liveRatio u).den addr
    (slotDegree S) enough
  filter_upwards [rows,start,clocks,preludeBounds,geometry] with n installed startup caps prelude geo
  intro hn p M data V inst G W P cut I A base rate Y
  have entered := startup ((D).tagsFit n) (dispatchClock hn) (I.branch.copy.memory ()) I.pairStartTag
  have actual : ∀ z : (V.selection (M := M)).Choices, let chain := selectedChain (V := V) (M := M) z
      let out := (V.selection (M := M)).finalState z
      out.maxWireWidth ≤ n ∧ ∀ v, chain.occurrences (fun _ => 1) v ≤ n := by
    have h := geo.2.2.2.2 (laneLabels _ _ V.lanes) V.dimension le_rfl M.algebra
      (B.compressorValues hn M) (B.compressorValues_solution hn M)
    unfold selectedChain VirtualPairs.selection
    rw [V.scanState_pairInput]
    exact h
  refine ⟨paperTerminalOfRated B u c labels E addr positive data V W P cut I A raw scanRate 0 Y
    entered.2.1 entered.1 (installed hn p M data V W P cut I A Y) caps geo.1 geo.2.1 geo.2.2.1
    (fun z => (actual z).1) (fun z => (actual z).2) ?_⟩
  exact prelude hn V ((D).tagsFit n) (dispatchClock hn) M rate (I.branch.copy.memory ()) Y

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
