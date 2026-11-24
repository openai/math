import OAI.Computability.VPVNP.CompressorInitialLiveBoundary
import OAI.Computability.VPVNP.CompressorInitialPairInput
import OAI.Computability.VPVNP.LiveVirtualPairOrdinalData

/-! # The physical startup graph of the actual virtual pair

The compiled ratio reserves the same lanes as the analytic block count.
The physical cursor's base and lane coordinate order agrees with the graph
of the mathematical virtual pair after the dimension cast. Thus its true
startup reports install the boundary for the exact state used in the
monomial expansion, on the same eleven public operands and incoming memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorRouting CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair
open CompressorRecords CompressorRecords.ScheduledTrace CompressorRecords.DescriptorSpace
open PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open scoped Fin.CommRing
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)

attribute [local irreducible] BlockProgram.script BlockProgram.layout InitialTransferred.bootstrap CursorNetwork.cursorState

theorem VirtualPairs.scanState_pairInput :
    V.scanState = pairInput S (laneLabels _ _ V.lanes) V.dimension := by
  have bucket : virtualBucket n = 2^roundedUp 1 4 n := by
    simp only [virtualBucket,roundedUp_eq,Nat.cast_one,Nat.cast_ofNat]
  unfold pairInput
  rw [bucket]

local notation "addr" => D.addressFactor
local notation "w" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "A" => BlockProgram.script B

theorem VirtualPairs.cursorState_eq (sum : 1 < b+l) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0)) :
    cursorState (cursorCoordinateLabels b l) sum hd
      (ramFieldBits (virtualBucket n) w : RAMSystem (virtualBits addr n) → ℕ) = V.scanState :=
  (initial_pairInput S addr n l V.lanes V.dimension sum hd).symm.trans V.scanState_pairInput.symm

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- The initial descriptor interval and its endpoint, reindexed to the
virtual pair's own state, before its first shrinking visit. -/
theorem VirtualPairs.initial_boundary (base clk : ℕ) (terminal : PairTable) (pub : Fin 11 → Word w)
    (incoming : Memory w) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0))
    (physical : InitialLive B f hf (blockRatio u).num (blockRatio u).den addr n base clk terminal pub incoming hd) :
    let boot := InitialTransferred.bootstrap B (blockRatio u).num (blockRatio u).den
    let L := BlockProgram.layout B base (initialPositions addr n) T
    let mem := after incoming (eventLog (cursorStartupLogs boot pub addr n base incoming
      (A).initial.length (A).block.length (A).size))
    StartupResult boot (A).plan terminal pub addr n base incoming clk ∧
      ∃ initial : InitialInterval B base (initialPositions addr n) T (sourceCap pub clk) (BlockClock.small B addr n)
        b l (initialWidth addr n) pub mem,
        Boundary (CurrentResident.resident B f hf ⟨leafLayer (siteOrder V.scanState),.cursor⟩ L (endAddress L) n
          (cursorFrame L (S.degreeExponent 0) b l (initialWidth addr n))) pub (levelWords L : Word w)
          (directoryRows L) 4 [] V.scanState initial.interval.segment.memory ∧
        RAMBuckets.cost Report.probes initial.interval.source.logs ≤ initialRate B*(initialPositions addr n+1) ∧
        BlockClock.small B addr n+3 ≤ sourceCap pub clk ∧
        sourceCap pub clk+24 = clockAt pub clk Stage.online := by
  unfold InitialLive at physical
  rw [blockRatio_floor] at physical
  obtain ⟨setup,sum,initial,ready,cost,slack,clock⟩ := physical
  have eqn := V.cursorState_eq sum hd
  exact ⟨setup,initial,eqn ▸ ready,cost,slack,clock⟩

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
