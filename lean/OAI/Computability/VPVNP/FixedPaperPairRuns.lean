import OAI.Computability.VPVNP.LiveVirtualPairPaperTerminal
import OAI.Computability.VPVNP.LiveVirtualPairScanSelection
import OAI.Computability.VPVNP.LiveCompressedPairDescriptorRoom
import OAI.Computability.VPVNP.CompressorNativePassRates
import OAI.Computability.VPVNP.FixedCompressedPairDiagonal

/-! # Choosing the finite compressed-pair program before the exceptional length

The fixed table computes the same descriptor and terminal paths used by the
algebraic expansion. The length threshold precedes the field model, its scalar
advice and every valid nominated group. All ring-specific work at that length
uses a single finite model and its actual evaluated template parameters.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open LabelEvaluator CompressorRecords ScheduledTrace DescriptorSpace
open PairStages PairStages.Group PairStages.Group.CompressedPaths LocalCount
open scoped Fin.CommRing

set_option quotPrecheck false
attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs CompressedPair.components PairSimulation.TerminalProgram.workers

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (u : PairExponents B.growthConstant)
  (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry) (E : UniversalMachine.Program)
  (addr : ℕ) (positive : 1 ≤ addr) (C : ℕ) (hC : c.circuitExponent = C)

local notation "D" => paperProgram B u c labels E addr positive
local notation "script" => BlockProgram.script B

/-- At the specified length, the real selected shrinking and refresh workers
run in their actual native calendar windows. -/
abbrev PaperPasses (raw n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (V : (D).VirtualPairs B u hn C) (p : Nat.Primes)
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn C)),
    let G := (D).executionGroup n ((D).tagsFit n) (dispatchClock hn)
    let pub := publicWords G
    let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
    let T := blockCount (u.θ : ℝ) n
    let P := initialPositions addr n
    let L := BlockProgram.layout B base P T
    let f := B.compressorValues hn M
    let ok := B.compressorValues_solution hn M
    let data := CompiledResident.payload (w := wordBits addr n) B f ok base P T n
    LocatedRuns (V.nativeResident f ok base data) pub (levelWords L : Word (wordBits addr n))
      (directoryRows L) (sourceCap pub (fuel G)) (BlockClock.small B addr n) (nativePassRate script raw * P) T P n

/-- For the same descriptor execution and canonical finite payload parser,
the terminal stages act on the actual memory entering this nominated pair. -/
abbrev PaperTerminals (raw n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
    (data : (D).ScalarData B hn M) (V : (D).VirtualPairs B u hn C) [NeZero (virtualBits ((D).addressFactor) n)],
    let G := (D).executionGroup n ((D).tagsFit n) (dispatchClock hn)
    ∀ (W : Conditions G (2^G.g.d) G.g.H) (P : PairStageConditions G (2^G.g.d) G.g.H)
      (cut : 1+B.denseCount n C*(D).counterWidth n ≤ n^c.deltaPower)
      (I : VirtualPairs.PhysicalInput data W P hC labels cut)
      (A : CanonicalScan data V (VirtualPairs.exterior data W P hC labels cut I)
        (VirtualPairs.modelIndex data W P hC labels cut I) (physicalNomination hC I.μ)),
      let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
      let rate := nativePassRate script raw * initialPositions addr n
      ∀ Y : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) c labels base
        (fuel G) rate (publicWords G) (I.branch.copy.memory ()),
        Nonempty (V.PaperTerminal data W P hC labels cut I A rate Y)

set_option maxHeartbeats 1200000 in
/-- Compile the per-pass and per-vertex physical source proofs into the
complete group-path specification at the fixed program's actual prefix. -/
theorem eventually_pairRuns_of_nativeStages (raw : ℕ) (enough : max S.laneBits 5 ≤ addr)
    (passes : ∀ᶠ n : ℕ in atTop, PaperPasses B u c labels E addr positive C raw n)
    (terminal : ∀ᶠ n : ℕ in atTop, PaperTerminals B u c labels E addr positive C hC raw n) :
    ∀ᶠ n : ℕ in atTop, (D).PairRuns B u C hC labels n := by
  obtain ⟨hd,initial⟩ := eventually_paperStartup.{0} B u c labels E addr positive ((le_max_left ..).trans enough)
  filter_upwards [passes,terminal,initial,eventually_canonicalScan (D) B u C enough,
    eventually_scan_prefix (D) B u C enough,eventually_descriptor_room B u c labels E addr positive]
    with n perPass perTerminal starts scan sizes room
  intro hn p M data fit V W P cut
  let : NeZero (virtualBits ((D).addressFactor) n) := ⟨(Nat.zero_lt_one.trans V.dimension).ne'⟩
  apply V.compressedCalls_of_nativeRuns data fit W P hC labels cut
  intro I
  let G := (D).executionGroup n ((D).tagsFit n) (dispatchClock hn)
  let ws := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
  let rate := nativePassRate script raw * initialPositions addr n
  obtain ⟨workspace,setup,start⟩ := starts ((D).tagsFit n) (dispatchClock hn) (I.branch.copy.memory ()) I.pairStartTag
  obtain ⟨A⟩ := scan hn V p M data (VirtualPairs.exterior data W P hC labels cut I)
    (VirtualPairs.modelIndex data W P hC labels cut I) (physicalNomination hC I.μ)
  obtain ⟨_,_,controls⟩ := room ((D).tagsFit n) (dispatchClock hn)
  let f := B.compressorValues hn M
  let ok := B.compressorValues_solution hn M
  obtain ⟨Y⟩ := V.paperDescriptor_of_runs f ok c labels ws (fuel G) rate (publicWords G) (I.branch.copy.memory ())
    hd (start f ok) (controls _ le_rfl) (sizes hn V M.algebra f ok) (perPass hn V p M)
  obtain ⟨Q⟩ := perTerminal hn p M data V W P cut I A Y
  exact ⟨V.nativeRunsOfPaperTerminal data fit W P hC labels cut I A rate Y rfl workspace setup Q⟩

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
