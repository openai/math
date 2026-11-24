import OAI.Computability.VPVNP.LiveCompressedPairClockBundle
import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary
import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan
import OAI.Computability.VPVNP.FixedProgramOperandFits

/-! # Actual group and finite-model clocks for a selected virtual pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds CompressorRecords ScheduledTrace LiveProgram CompressedPair
open LabelEvaluator BurstRAM PairSimulation LocalHistory

universe v
variable {K : Type v} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
variable {D : FixedProgramDiagonal.Program} {u : PairExponents B.growthConstant}
variable {n C : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)
variable {p : Nat.Primes} {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
variable {bs : Bootstrap} {initial phases raw site q link : ℕ}
variable (h : BranchClocks.{0} B u D.addressFactor bs initial phases raw site q link n)
variable (numerator : D.numerator = (liveRatio u).num) (denominator : D.denominator = (liveRatio u).den)
local notation "κ" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "sel" => V.selection (M := M)
local notation "T" => blockCount (u.θ : ℝ) n
local notation "P" => initialPositions D.addressFactor n
local notation "w" => wordBits D.addressFactor n
local notation "scr" => BlockProgram.script B
local notation "small" => BlockClock.small B D.addressFactor n
local notation "bootBound" => TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit + 1
local notation "coefficient" => terminalCoefficient S.baseDegree S.steps B.recordLimit (bootBound) 1 site

include numerator denominator in
private theorem group_sizes :
    2^(D.geometry n).d = processorCount D.addressFactor n ∧ (D.geometry n).H = liveCapacity u n := by
  rw [paperGeometry_eq D B u numerator denominator n]
  exact ⟨rfl,rfl⟩

include h numerator denominator

/-- All final site and total traversal bounds use the finite-model
coefficient chain actually selected by the virtual pair. -/
theorem VirtualPairs.terminalClock :
    ∀ z : (sel).Choices, let chain := selectedChain (V := V) (M := M) z
      let Y := (sel).finalState z
      320*branchAccesses V.scanState Y chain coefficient q n ≤ 2^(D.geometry n).d*(D.geometry n).H ∧
        ∀ v, siteAccesses Y chain site q n v+9 ≤ (D.geometry n).H := by
  obtain ⟨processors,capacity⟩ := group_sizes (n := n) numerator denominator
  rw [processors,capacity]
  change ∀ z : (B.execute κ ok T le_rfl V.scanState).Choices, let E := B.execute κ ok T le_rfl V.scanState
    let chain := E.termChain (B.records κ ok T le_rfl V.scanState) z
    320*branchAccesses V.scanState (E.finalState z) chain coefficient q n ≤
      processorCount D.addressFactor n*liveCapacity u n ∧
      ∀ v, siteAccesses (E.finalState z) chain site q n v+9 ≤ liveCapacity u n
  rw [V.scanState_pairInput]
  exact h.terminal (laneLabels _ _ V.lanes) V.dimension le_rfl M.algebra κ ok

/-- The live program's actual initial and recursive descriptor reports
receive the group and per-burst bounds in the geometry used by the compiler. -/
theorem VirtualPairs.onlineClock
    {resident : Resident B κ ok w} {past : List (SelectedLevel B κ ok)}
    {pub : Fin 11 → Word w} {pitch : Word w} {m : Memory w} {cap total : ℕ}
    {origin : PassOrigins B κ ok (sel)} {W : (sel).MapWitnesses κ} {readers : ExecutionReaders (sel) W}
    (start : QuietInterval scr pub cap small (some 0) m)
    (first : RAMBuckets.cost Report.probes start.source.logs ≤ initialRate B*(P+1))
    (result : Result resident pub pitch total cap small (T*(S.steps+1)*(nativePassRate scr raw*P)+4)
      (sel) origin W readers past start.segment.state start.segment.memory)
    (G : PairStages.Group) (clock : G.clock = n^10000) (z : (sel).Choices) :
    let core := start.combinedCore result.trace result.source z
    64*RAMBuckets.cost Report.probes core.logs ≤ 2^(D.geometry n).d*(D.geometry n).H ∧
      ∀ r ∈ core.logs, r.probes+11 ≤ (D.geometry n).H ∧ r.events.length+101 ≤ G.clockAt LiveProgram.Stage.pair := by
  obtain ⟨processors,capacity⟩ := group_sizes (n := n) numerator denominator
  rw [processors,capacity]
  exact h.selectedOnline (laneLabels _ _ V.lanes) V.dimension start first result G clock z

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
