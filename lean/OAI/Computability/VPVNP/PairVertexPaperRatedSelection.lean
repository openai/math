import OAI.Computability.VPVNP.PairVertexRatedBoundarySelection
import OAI.Computability.VPVNP.PairVertexRatedRoles
import OAI.Computability.VPVNP.PairVirtualDescriptorHistory
import OAI.Computability.VPVNP.LiveVirtualPairQuietPrelude

/-! # The rated terminal branch of the actual finite-model descriptor -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM LiveProgram

variable {w cap : ℕ} {old new : Stage → PairTable} {pub : Fin 11 → Word w} {m : Memory w}
  (q : QuietPrefix old pub cap m) (same : old = new)

/-- Identify the fixed prelude under an equality of the installed instruction banks. -/
def QuietPrefix.reindexWorkers : QuietPrefix new pub cap m := same ▸ q

theorem QuietData.reindexWorkers {lo width pref rows : ℕ}
    {post : (Fin width → Bool) → Memory w → Prop}
    (d : QuietData q lo width pref rows post) :
    QuietData (q.reindexWorkers same) lo width pref rows post := by
  cases same
  exact d

end PairSimulation.TerminalLink

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM PrivateRAM
open CompressorRecords DescriptorSpace
open PairSimulation LocalHistory NetworkKernel LiveProgram CompressedPair TerminalLink
open CutSchedule ExponentTrace
open PairStages.Group.Auxiliary PairStages.Group.CompressedPaths SourceTransport
open TraversalRows TraversalRoles

open scoped Fin.CommRing
set_option quotPrecheck false
attribute [local irreducible] VertexImage.template VertexImage.placement PhysicalScanData.physical
  TerminalProgram.workers BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState CursorBounds.wordBits stateScanPhase
  onlinePost QuietPrefix.reindexWorkers

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {u : PairExponents B.growthConstant} {n : ℕ} {hn : 2 ≤ n}
  {ht : 21 ≤ 2 ^ (D.geometry n).w} {hc : 44 ≤ n ^ 10000} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
  {data : D.ScalarData B hn M} {V : D.VirtualPairs B u hn D.constants.circuitExponent}
  [NeZero (virtualBits D.addressFactor n)]
  {ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)} {i : D.groupIndices n}
  {μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht hc)}
  (scan : CanonicalScan data V ξ i (physicalNomination rfl μ)) (z : (V.selection (M := M)).Choices)
  {hg : D.constants.motifLabels = Fintype.card B.Entry}
  (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den)

local notation "G" => D.executionGroup n ht hc
local notation "ww" => wordBits D.addressFactor n
local notation "pub" => terminalOperands (G)
local notation "cap" => clockAt (publicWords (G)) (fuel (G)) CompressedPair.Stage.terminal
local notation "X" => V.scanState
local notation "Y" => (V.selection (M := M)).finalState z
local notation "κ" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "T" => blockCount (u.θ : ℝ) n
local notation "pos" => initialPositions D.addressFactor n
local notation "baseBits" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "laneBits" => reservedLanes B u n
local notation "start" => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
local notation "names" => entryOrdinal B D.constants hg
local notation "parts" => paperSegments B u D.constants hg
local notation "code" =>
  TerminalProgram.nativeSegments B D.constants D.numerator D.denominator names
local notation "old" => TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit parts
local notation "new" => TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit code

include num den in
/-- The physical role bank selected by the paper parameters. -/
theorem paper_native_workers : (old) = (new) := by rw [num, den]; rfl

variable {rate : ℕ} {input : Memory (wordBits D.addressFactor n)}
  (desc : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M)
    D.constants hg ((LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n))
    (fuel (D.executionGroup n ht hc)) rate (terminalOperands (D.executionGroup n ht hc)) input)
  (q : QuietPrefix (TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit
      (paperSegments B u D.constants hg)) (terminalOperands (D.executionGroup n ht hc))
    (clockAt (publicWords (D.executionGroup n ht hc)) (fuel (D.executionGroup n ht hc))
      CompressedPair.Stage.terminal)
    (onlinePost (desc.paths z)))
  (quiet : VirtualPairs.PaperDescriptor.QuietData desc z q)

local notation "same" => paper_native_workers (B := B) (hg := hg) num den
local notation "q₀" => q.reindexWorkers (same)
local notation "quiet₀" => quiet.reindexWorkers q (same)
local notation "L" => BlockProgram.layout B start pos T
local notation "tab" =>
  (⟨0, by unfold BlockProgram.layout; change 0 < 6; decide⟩ : Fin (L).shape.tables)
local notation "layers" => selectedLayers B κ ok T le_rfl (X) z
local notation "lo" => endAddress (L) + words B.recordLimit (layers)
local notation "snap₀" =>
  CompiledResident.payload (w := ww) B κ ok (start : BurstRAM.Word ww) pos T n
local notation "vs" => executeLevels B κ ok T le_rfl (X) z
local notation "calendar" => onlinePost (desc.paths z)
local notation "scanRate" => VertexImage.RatedRoles.scan B names
local notation "enter" =>
  TerminalProgram.VertexEntry B κ ok T le_rfl (X) z (L) tab baseBits laneBits
  (pub) (calendar)
local notation "past" => SelectedPayloadHistory.Past B κ ok (L) (snap₀) (vs)

private theorem sameReads {w : ℕ} (h : BurstRAM.Word w) (m : Memory w) :
    Agree (workerCell h) m m := fun _ _ => rfl

local notation "identityReads" => sameReads (header (pub)) (q₀).traversalRows.val.memory


/-- The native vertex rows selected from this literal descriptor, with its quiet prefix,
actual memory and scan rate. -/
def VirtualPairs.PaperDescriptor.RatedTerminalRows : Prop :=
  RatedSelection scan z names (endAddress (L)) (pub 4).val (pub 5).val (cap) (pub) (q₀) (lo)
      (q₀).traversalRows.val.memory (quiet₀).layout (quiet₀).clock (quiet₀).headerFit (quiet₀).below
      (identityReads) 1 scanRate

set_option maxHeartbeats 2000000 in
-- The workspace equality is transported through the four dependent vertex-entry indices.
/-- The selected native branch starts at the literal descriptor's calendar exit.
The same quiet prefix supplies its wire layout, historical rows and role data. -/
theorem VirtualPairs.PaperDescriptor.ratedSelection (large : 128 ≤ n)
    (workspace : (pub 2).val = start) (tag : (PairTag.address (pub)).val < (pub 2).val + 6)
    (rated : ∀ m₀ m₁ reference m : Memory ww,
      V.RatedAtBoundary data.advice ξ i μ names κ ok scan.leafSites z baseBits laneBits
        (initialWidth D.addressFactor n) n 1 scanRate m₀ m₁ reference m)
    (roles : ∀ bits reference, ((enter) reference bits) → ((past) reference) →
      ∀ (j : Fin (siteOrder (Y)).length) m, LinkedVertexMemory (G) reference j.val m →
      V.SelectedRowsAt data.advice ξ i μ names κ ok scan.leafSites z m 1 scanRate) :
    VirtualPairs.PaperDescriptor.RatedTerminalRows scan z num den desc q quiet := by
  unfold VirtualPairs.PaperDescriptor.RatedTerminalRows
  have positions : (X).positions = pos := by
    rw [V.scanState_pairInput]
    exact pairInput_positions S _ _
  let L' := BlockProgram.layout B (pub 2).val (X).positions T
  have alloc : L' = (L) := by dsimp only [L']; rw [workspace, positions]
  have raw := desc.current_at_online z workspace
  have handoff := TerminalPrefix.Linked.handoff_of_transfer (pub) (desc.post z) tag
  apply (congrArg (fun base =>
    RatedSelection scan z names base (pub 4).val (pub 5).val (cap) (pub) (q₀) (lo)
      (q₀).traversalRows.val.memory (quiet₀).layout (quiet₀).clock (quiet₀).headerFit (quiet₀).below
      (identityReads) 1 scanRate) (congrArg endAddress alloc)).mp
  apply scan.ratedSelection_of_boundary z names (quiet₀).layout (quiet₀).clock (quiet₀).headerFit
    (quiet₀).below 1 scanRate large (payload := snap₀)
  · exact raw
  · exact handoff
  · intro bits a tape
    have chosen : ((enter) a.val.memory bits) ∧ ((past) a.val.memory) :=
      (quiet₀).entry bits a tape
    refine ⟨chosen.1.changeLayout alloc.symm rfl, ?_⟩
    simpa only [workspace, positions] using chosen.2
  · exact rated _ _
  · intro bits a entry retained j m later
    apply roles bits a.val.memory _ _ j m later
    · exact entry.changeLayout alloc rfl
    · simpa only [workspace, positions] using retained

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
