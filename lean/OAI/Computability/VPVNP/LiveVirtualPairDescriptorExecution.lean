import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary
import OAI.Computability.VPVNP.CompressorDetailedResident
import OAI.Computability.VPVNP.CompressorScheduledExecution

/-! # The selected virtual pair's descriptor execution and retained data

The descriptor's actual initial memory is obtained after the eight linked
startup calls and four fixed cursor visits. It is the memory used for the
first shrinking pass of the virtual pair. The empty past carries its payload
invariant, and the native execution retains every selected pass's data at
the physical terminal boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorRouting CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open CompressorRecords CompressorRecords.ScheduledTrace CompressorRecords.DescriptorSpace
open PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
local notation "addr" => D.addressFactor
local notation "ww" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "A" => BlockProgram.script B
local notation "P" => initialPositions D.addressFactor n
local notation "X" => VirtualPairs.scanState V
local notation "E" => B.execute f hf T le_rfl (VirtualPairs.scanState V)
local notation "small" => BlockClock.small B D.addressFactor n

attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState

/-- A common length threshold supplies graph and wire-width bounds on all
partial branches before the scalar algebra and the virtual pair are chosen. -/
theorem eventually_scan_prefix (D : FixedProgramDiagonal.Program) (B : S.Templates) (u : PairExponents B.growthConstant)
    (C : ℕ) (haddr : max S.laneBits 5 ≤ D.addressFactor) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) (R : Type*) [CommRing R]
      (f : B.Entry → R) (hf : B.IsSolution f), PrefixLevelScale.Within (initialPositions D.addressFactor n) n
        (B.execute f hf (blockCount (u.θ : ℝ) n) le_rfl V.scanState) := by
  filter_upwards [PrefixLevelScale.eventually_execute B u D.addressFactor haddr] with n fits hn V R inst f hf
  rw [V.scanState_pairInput]
  exact fits _ V.dimension le_rfl R f hf

/-- The resident descriptor data for the virtual pair's native execution, with its initial
cursor layer, physical layout, cursor frame and selected payload history. -/
noncomputable abbrev VirtualPairs.nativeResident (base : ℕ) (payload : SelectedPayloadHistory.Data (w := ww) B f hf) :
    ScheduledTrace.Resident B f hf ww :=
  let L := BlockProgram.layout B base P T
  DetailedResident.resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n
    (cursorFrame L (S.degreeExponent 0) b l (initialWidth addr n)) payload

theorem VirtualPairs.descriptor_execution (base clk rate : ℕ) (terminal : PairTable) (pub : Fin 11 → Word ww)
    (incoming : Memory ww) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0))
    (physical : InitialLive B f hf (blockRatio u).num (blockRatio u).den addr n base clk terminal pub incoming hd)
    (payload : SelectedPayloadHistory.Data (w := ww) B f hf)
    (smallBounds : Schedule.Online.Run.ControlBounds (A).plan small (w := ww))
    (size : PrefixLevelScale.Within P n E)
    (build : let L := BlockProgram.layout B base P T
      LocatedRuns (V.nativeResident f hf base payload) pub (levelWords L : Word ww) (directoryRows L)
        (sourceCap pub clk) small rate T P n) :
    let boot := InitialTransferred.bootstrap B (blockRatio u).num (blockRatio u).den
    let L := BlockProgram.layout B base P T
    let mem := after incoming (eventLog (cursorStartupLogs boot pub addr n base incoming
      (A).initial.length (A).block.length (A).size))
    StartupResult boot (A).plan terminal pub addr n base incoming clk ∧
      ∃ initial : InitialInterval B base P T (sourceCap pub clk) small b l (initialWidth addr n) pub mem,
        RAMBuckets.cost Report.probes initial.interval.source.logs ≤ initialRate B*(P+1) ∧
        small+3 ≤ sourceCap pub clk ∧ sourceCap pub clk+24 = clockAt pub clk Stage.online ∧
        Nonempty (ScheduledTrace.Result (V.nativeResident f hf base payload) pub (levelWords L : Word ww) (directoryRows L)
          (sourceCap pub clk) small (T*(S.steps+1)*rate+4) E (executeOrigins B f hf T le_rfl X) _
          (nativeReaders (B := B) (f := f) (hf := hf) le_rfl X) [] (some 0) initial.interval.segment.memory) := by
  let L := BlockProgram.layout B base P T
  obtain ⟨setup,initial,ready,work,slack,hclock⟩ := V.initial_boundary f hf base clk terminal pub incoming hd physical
  refine ⟨setup,initial,work,slack,hclock,?_⟩
  have total := BlockProgram.directory_rows B base P T
  have start := BlockProgram.initial_length B
  have live : Boundary (V.nativeResident f hf base payload) pub (levelWords L : Word ww)
      (directoryRows L) 4 [] X initial.interval.segment.memory :=
    ⟨ready.bank,ready.tag,ready.ordinalValue,ready.totalValue,ready.stride,ready.stored,SelectedPayloadHistory.Past.empty⟩
  have bounds : Schedule.Online.Run.ControlBounds (A).plan (sourceCap pub clk) (w := ww) :=
    ⟨smallBounds.tags,smallBounds.calendar.trans (by omega),smallBounds.launch.trans (by omega)⟩
  change directoryRows L = _ at total
  dsimp only at build
  change LocatedRuns _ pub _ (directoryRows L) _ _ _ _ _ _ at build
  rw [total] at live build ⊢
  rw [← start] at live
  exact execute_of_local le_rfl X initial.interval.segment.memory bounds smallBounds build size live

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
