import OAI.Computability.VPVNP.PairVertexRatedSelection
import OAI.Computability.VPVNP.PairVertexRatedEntry
import OAI.Computability.VPVNP.PairVertexRatedTerminalClock
import OAI.Computability.VPVNP.PairVirtualOrdinalCalls
import OAI.Computability.VPVNP.PairVirtualRootPayload

/-! # Certified vertex rows on the physical shared-bit path of the selected calendar -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory

/-- Transport a checked vertex entry to the same packed directory and table index. -/
theorem VertexEntry.changeLayout {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → A} {ok : B.IsSolution f} {lanes T : ℕ}
    {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
    {z : (B.execute f ok T hT X).Choices} {L L' : Layout} {tab : Fin L.shape.tables}
    {tab' : Fin L'.shape.tables} {b l w : ℕ} {pub : Fin 11 → BurstRAM.Word w}
    {m m' : Memory w} {bits : Fin ((B.execute f ok T hT X).finalState z).totalWidth → Bool}
    (entry : VertexEntry B f ok T hT X z L tab b l pub m m' bits)
    (same : L = L') (index : tab.val = tab'.val) :
    VertexEntry B f ok T hT X z L' tab' b l pub m m' bits := by
  subst L'
  exact (Fin.ext index : tab = tab') ▸ entry

end PairSimulation.TerminalProgram

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM PrivateRAM
open CompressorRecords DescriptorSpace
open PairSimulation LocalHistory NetworkKernel LiveProgram CompressedPair TerminalLink
open CutSchedule ExponentTrace
open PairStages.Group.Auxiliary PairStages.Group.CompressedPaths SourceTransport TraversalRows

open scoped Fin.CommRing
open private scanWords scanMachine capacity from OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

set_option quotPrecheck false
attribute [local irreducible] VertexImage.template VertexImage.placement PhysicalScanData.physical
  TerminalProgram.workers BlockSchedule.Templates.execute BlockProgram.layout
  CursorBounds.wordBits CursorNetwork.cursorState stateScanPhase

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {u : PairExponents B.growthConstant} {n : ℕ} {hn : 2 ≤ n}
  {ht : 21 ≤ 2 ^ (D.geometry n).w} {hc : 44 ≤ n ^ 10000} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
  {data : D.ScalarData B hn M} {V : D.VirtualPairs B u hn D.constants.circuitExponent}
  [NeZero (virtualBits D.addressFactor n)]
  {ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)} {i : D.groupIndices n}
  {μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht hc)}
  (scan : CanonicalScan data V ξ i (physicalNomination rfl μ)) (z : (V.selection (M := M)).Choices)
  (names : B.Entry ≃ Fin D.constants.motifLabels)

local notation "G" => D.executionGroup n ht hc
local notation "ww" => wordBits D.addressFactor n
local notation "pub" => terminalOperands (G)
local notation "cap" => clockAt (publicWords (G)) (fuel (G)) CompressedPair.Stage.terminal
local notation "X" => V.scanState
local notation "Y" => (V.selection (M := M)).finalState z
local notation "κ" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "T" => blockCount (u.θ : ℝ) n
local notation "L" => BlockProgram.layout B (pub 2).val (X).positions T
local notation "tab" =>
  (⟨0, by unfold BlockProgram.layout; change 0 < 6; decide⟩ : Fin (L).shape.tables)
local notation "code" =>
  TerminalProgram.nativeSegments B D.constants D.numerator D.denominator names
local notation "bank" => TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit code
local notation "vs" => executeLevels B κ ok T le_rfl (X) z
local notation "shape" => BlockProgram.allocationShape B
local notation "ref" => scanMachine ww
local notation "link" => FinalBits.template_linked (scanWords ww)
local notation "fit" => capacity scan z

variable {baseBits laneBits initialWidth inputN : ℕ}
  {online calendar : Memory (wordBits D.addressFactor n)}
  {payload : SelectedPayloadHistory.Data (w := wordBits D.addressFactor n) B
    (B.compressorValues hn M) (B.compressorValues_solution hn M)}
  {q : QuietPrefix (TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit
    (TerminalProgram.nativeSegments B D.constants D.numerator D.denominator names))
    (terminalOperands (D.executionGroup n ht hc))
    (clockAt (publicWords (D.executionGroup n ht hc)) (fuel (D.executionGroup n ht hc))
      CompressedPair.Stage.terminal) calendar} {lo : ℕ}
  (layout : FinalBits.Worker.Layout (terminalOperands (D.executionGroup n ht hc))
    q.traversalRows.val.memory lo ((V.selection (M := M)).finalState z).totalWidth)
  (clock : 54 ≤ clockAt (publicWords (D.executionGroup n ht hc)) (fuel (D.executionGroup n ht hc))
    CompressedPair.Stage.terminal)
  (room : (header (terminalOperands (D.executionGroup n ht hc))).val + 32 ≤
    2 ^ (wordBits D.addressFactor n))
  (below : lo + ((V.selection (M := M)).finalState z).totalWidth ≤
    (header (terminalOperands (D.executionGroup n ht hc))).val)

local notation "saved" => CursorRAM.ScheduleInit.inputs (CursorRAM.encode ww (directoryBase (L)))
  (CursorRAM.encode ww 1) baseBits laneBits (S.degreeExponent 0) initialWidth (incidenceStart (L) 0)
local notation "resident" => CurrentResident.resident B κ ok ⟨leafLayer (siteOrder (X)), .cursor⟩
  (L) (endAddress (L)) inputN (saved)
local notation "enter" =>
  TerminalProgram.VertexEntry B κ ok T le_rfl (X) z (L) tab baseBits laneBits
  (pub) calendar
local notation "past" => SelectedPayloadHistory.Past B κ ok (L) payload (vs)
local notation "linked" => LinkedVertexMemory (G)
local notation "phys" =>
  PhysicalScanData.physical (Y) (ref) Fin.castSucc (Function.Embedding.refl _)
  0 10 link rfl 0 rfl (fun _ => 0) 0 fit shape B.recordLimit code (pub) (cap)
  q.traversalRows.val.memory q.traversalRows.val.memory lo layout clock room below (fun _ _ => rfl)

/-- Transport the retained rows and the measured role contracts along the
actual shared-bit tape used by each canonical arc assignment. The later
site frames use precisely this path's physical post-memory. -/
theorem CanonicalScan.ratedSelection_of_boundary (power scanRate : ℕ) (large : 128 ≤ n)
    (boundary : ScheduledTrace.Boundary (resident) (pub) (levelWords (L) : BurstRAM.Word ww)
      (directoryRows (L)) (directoryRows (L)) (vs) (Y) online)
    (handoff : Agree ((pub 2).val + 6 ≤ ·) online calendar)
    (picked : ∀ bits (a : q.BitPaths), a.val.choices = FinalBits.calls bits ++ [[]] →
      ((enter) a.val.memory bits) ∧ ((past) a.val.memory))
    (rated : ∀ reference m, V.RatedAtBoundary data.advice ξ i μ names κ ok scan.leafSites z
      baseBits laneBits initialWidth inputN power scanRate online calendar reference m)
    (roles : ∀ bits (a : q.BitPaths), ((enter) a.val.memory bits) → ((past) a.val.memory) →
      ∀ (j : Fin (siteOrder (Y)).length) m, ((linked) a.val.memory j.val m) →
      V.SelectedRowsAt data.advice ξ i μ names κ ok scan.leafSites z m power scanRate) :
    RatedSelection scan z names (endAddress (L)) (pub 4).val (pub 5).val cap (pub)
      q lo q.traversalRows.val.memory layout clock room below (fun _ _ => rfl) power scanRate := by
  have fromPath (x : (scan.arc z).Path) :
      ((enter) ((phys) x).val.memory (scan.sharedBits z x)) ∧ ((past) ((phys) x).val.memory) := by
    apply picked
    exact (PhysicalScanData.physical_choices ..).trans
      (congrArg (· ++ [[]]) (PhysicalScanData.calls (Y) (ref) Fin.castSucc
        (Function.Embedding.refl _)
        0 10 link rfl 0 rfl (fun _ => 0) 0 fit x))
  refine ⟨fun x => (fromPath x).1.storedOrdinal room, ?_⟩
  intro x j m later
  have ⟨entry, retained⟩ := fromPath x
  have checks := roles _ ((phys) x) entry retained j m later
  have row := rated _ m boundary handoff _ entry j later checks (cap)
    (terminal_ordinal_room (G) large rfl)
  have fields := PhysicalScanData.payload (Y) (ref) Fin.castSucc (Function.Embedding.refl _)
    0 10 link rfl 0 rfl (fun _ => 0) 0 fit x
  have same : TerminalGatherGeometry.half (Y)
      (fun t => scan.sharedBits z x (Fin.cast (TerminalPrefix.width_sum (Y)) t)) =
      WireTensor.edgeAssignment (Y).network.src (Y).network.dst ((scan.arc z).payload x) :=
    congrArg (WireTensor.edgeAssignment (Y).network.src (Y).network.dst) fields.symm
  rw [← same]
  exact row

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
