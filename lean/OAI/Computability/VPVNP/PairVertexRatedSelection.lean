import OAI.Computability.VPVNP.PairVertexRatedRow
import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan
import OAI.Computability.VPVNP.LiveCompressedPairVertexAssembly
import OAI.Computability.VPVNP.LiveCompressedPairBranchCharge
import OAI.Computability.VPVNP.PairTerminalNativeTable

/-! # The physical vertex phase and its site charges on a canonical virtual pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM PrivateRAM CompressorRecords
  SourceTransport
open PairSimulation LocalHistory NetworkKernel LiveProgram CompressedPair TerminalLink CutSchedule
  ExponentTrace
open scoped Fin.CommRing
set_option quotPrecheck false
set_option genSizeOf false
attribute [local irreducible] VertexImage.template VertexImage.segments PhysicalScanData.physical
  TerminalProgram.workers
  BlockSchedule.Templates.execute CursorNetwork.cursorState CursorBounds.wordBits stateScanPhase
  VertexImage.placement
open private scanWords scanMachine capacity from OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

variable {k : Type} [Field k] {S : BlockSchedule k} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {model : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    {data : D.ScalarData B hn model} {u : PairExponents B.growthConstant} {V : D.VirtualPairs B u
      hn C}
    [NeZero (virtualBits D.addressFactor n)]
    {ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)} {i : D.groupIndices n} {μ :
      D.pairNom n C}
    (scan : CanonicalScan data V ξ i μ) (z : (V.selection (M := model)).Choices)

local notation "w" => CursorBounds.wordBits D.addressFactor n
local notation "Y" => (V.selection (M := model)).finalState z
local notation "κ" => B.compressorValues hn model
local notation "hf" => B.compressorValues_solution hn model
local notation "T" => blockCount (u.θ : ℝ) n
local notation "ord" => (siteOrder (Y)).entries
local notation "scanM" => scanMachine w
local notation "sl" => FinalBits.template_linked (scanWords w)
local notation "bitFit" => capacity scan z
local notation "shape" => BlockProgram.allocationShape B

variable {g : ℕ} (names : B.Entry ≃ Fin g) (rowBase counter grammar cap : ℕ)
  (pub : Fin 11 → BurstRAM.Word (CursorBounds.wordBits D.addressFactor n))
  {mem : Memory (CursorBounds.wordBits D.addressFactor n)}

local notation "geo" => VertexGeometry.segment D.constants (slotDegree S) D.numerator D.denominator
local notation "shr" => ShrinkVertexImage.shrinkSegment B names
local notation "ref" =>
  RefreshVertex.refreshSegment B (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride names
local notation "code" =>
  VertexImage.segments geo TerminalRootGather.segment LeafRole.segment shr ref
local notation "worker" => (VertexImage.template code).instantiate w pub
local notation "W" => TerminalProgram.workers shape B.recordLimit code

variable (q : QuietPrefix (TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit
    (TerminalProgram.nativeSegments B D.constants D.numerator D.denominator names)) pub cap mem)
  (lo : ℕ) (before : Memory (CursorBounds.wordBits D.addressFactor n))
  (layout : FinalBits.Worker.Layout pub before lo ((V.selection (M := model)).finalState
    z).totalWidth)
  (clock : 54 ≤ cap) (headerFit : (header pub).val + 32 ≤ 2 ^ (CursorBounds.wordBits
    D.addressFactor n))
  (below : lo + ((V.selection (M := model)).finalState z).totalWidth ≤ (header pub).val)
  (agree : Agree (workerCell (header pub)) before q.traversalRows.val.memory)

local notation "arc" => scan.arc z
local notation "parsers" => scan.sites z
local notation "fields" x =>
  WireTensor.edgeAssignment (Y).network.src (Y).network.dst ((arc).payload x)
local notation "physical" =>
  PhysicalScanData.physical (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10
  sl rfl 0 rfl (fun _ => 0) 0 bitFit shape B.recordLimit code pub cap before
    q.traversalRows.val.memory
  lo layout clock headerFit below agree
local notation "mem₀" x => ((physical) x).val.memory
local notation "frame" x => VertexFrame.Linked (header pub) counter grammar g (mem₀ x)
local notation "row₀" => VertexImage.RatedOrdinal B κ hf T le_rfl V.scanState z rowBase
  (VertexImage.placement code) worker counter grammar names.symm scan.leafSites

/-- The chosen physical shared-bit output supplies the reference for every
later site. Only the stored ordinal and the individual initialized root
rows, including their installed role costs, are required. -/
def RatedSelection (power scanRate : ℕ) : Prop :=
  (∀ x : (arc).Path, (mem₀ x) (header pub + 7).val = ((siteOrder (Y)).length : BurstRAM.Word w)) ∧
    ∀ (x : (arc).Path) (j : Fin (siteOrder (Y)).length) (m : Memory w),
      (frame x) j.val m → Nonempty (row₀ (fields x) cap m j n power scanRate)

variable {power scanRate : ℕ}
  (R : RatedSelection scan z names rowBase counter grammar cap pub q lo before layout clock
    headerFit
    below agree power scanRate)
  (counterEnd : counter + grammar + g ≤ (header pub).val)

local notation "visit" x =>
  SelectedSites (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10 sl rfl
  0 rfl (fun _ => 0) 0 bitFit (parsers) ord names.symm shape B.recordLimit pub q lo before layout
  clock headerFit below agree counter grammar x

/-- Use the same initialized row for forward execution, raw-tape decoding
and source report checks. The source and physical executions start on the
actual post-scan memory. -/
noncomputable def RatedSelection.selectedSites (x : (arc).Path) : visit x := by
  have localRows (j : Fin (siteOrder (Y)).length) (m : Memory w) (h : (frame x) j.val m) :=
    (R.2 x j m h).elim fun r => (show Nonempty (VertexImage.OrdinalRows B κ hf T le_rfl
      V.scanState z
      rowBase (VertexImage.placement code) worker counter grammar names.symm scan.leafSites
        (fields x)
      cap m j) from ⟨r.row⟩)
  let checked := VertexImage.selectedCalls B κ hf T le_rfl V.scanState z rowBase
    (VertexImage.placement code) worker counter grammar names.symm scan.leafSites (fields x)
    (mem₀ x) (VertexImage.template_contains code pub) localRows
  exact {
    reference := mem₀ x
    sourceMem := mem₀ x
    active := checked.1
    checks := checked.2
    stored := VertexImage.linked_finalSites (mem₀ x) headerFit counterEnd (R.1 x)
    sourceReady := VertexFrame.linked_initial (header pub) counter grammar g 0 (mem₀ x)
    physicalReady := VertexFrame.linked_initial (header pub) counter grammar g 0 (mem₀ x)
    agree := fun _ _ => rfl }


local notation "visit₀" =>
  R.selectedSites scan z names rowBase counter grammar cap pub q lo before layout
  clock headerFit below agree counterEnd

/-- The source branch associated with this certified family of physical
ordinal rows. Its vertex path uses the assignment of its own bit path. -/
noncomputable abbrev RatedSelection.branch :=
  selectedTerminalBranch (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10 sl rfl 0 rfl
    (fun _ => 0)
    0 bitFit (parsers) ord names.symm shape B.recordLimit pub q lo before layout clock headerFit
      below
    agree counter grammar (visit₀)

local notation "branch₀" => R.branch scan z names rowBase counter grammar cap pub q lo before layout
  clock headerFit below agree counterEnd
local notation "C₀" =>
  VertexReportBudget.coefficient S.baseDegree (Fintype.card B.Entry) 6 scanRate 0 0

/-- Both raw phase lists and the measured bound at every individual site,
on the exact same accepted five-phase trace. -/
theorem RatedSelection.chosenRows (hn₀ : 2048 ≤ n) (degree : S.baseDegree ≤ n)
    (labels : Fintype.card B.Entry ≤ n) (width : (Y).maxWireWidth ≤ n)
    (depth : ∀ v, (selectedChain (V := V) (M := model) z).occurrences (fun _ => 1) v ≤ n)
    (x : TerminalData (arc) (parsers)) :
    ∃ (bitMemory last : Memory w) (bits : Fin (Y).totalWidth → Bool) (reps : (Y).network.Site →
      Report w),
      ((branch₀).chosenTrace x).sharedBits.logs.map Prod.snd = FinalBits.Worker.reports pub 0
        bitMemory bits ∧
      ((branch₀).chosenTrace x).vertices.logs.map Prod.snd = (List.ofFn fun j => reps (ord j)) ++
        [VertexImage.closingReport pub last] ∧
      ∀ v, 1 + (reps v).probes ≤ siteAccesses (Y) (selectedChain (V := V) (M := model) z) C₀ power
        n v ∧
        (reps v).events.length + 107 ≤ n ^ 45 := by
  let ok := fun v (r : Report w) => 1 + r.probes ≤
    siteAccesses (Y) (selectedChain (V := V) (M := model) z) C₀ power n v ∧ r.events.length + 107
      ≤ n ^ 45
  obtain ⟨bits, reps, measured, vertices⟩ :=
    selectedTerminalBranch_rows (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10 sl rfl 0 rfl
      (fun _ => 0) 0 bitFit (parsers) ord names.symm shape B.recordLimit pub q lo before layout
      clock headerFit below agree counter grammar (visit₀) x.arcs x.choices ok
      (fun j m h y r run => (R.2 x.arcs j m h).elim fun q =>
        q.report_cost (VertexImage.template_contains code pub) hn₀ degree labels width (depth _) y
          r run)
  exact ⟨before,_,_,reps,bits,vertices,measured⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
