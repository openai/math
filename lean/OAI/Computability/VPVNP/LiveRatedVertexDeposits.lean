import OAI.Computability.VPVNP.PairVertexRatedSelection
import OAI.Computability.VPVNP.LiveSelectedVertexCounters
import OAI.Computability.VPVNP.LiveTerminalWorkerTransport
import OAI.Computability.VPVNP.PairTerminalFootprint

/-! # Counter deposits of the rated canonical vertex branch

The selected row certificates determine the physical reports. In the counter
interval, the resulting memory equals the fold of the selected preorder jobs'
exponents over the original pair memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM PrivateRAM CompressorRecords SourceTransport
open PairSimulation LocalHistory NetworkKernel LiveProgram CompressedPair TerminalLink CutSchedule ExponentTrace
open scoped Fin.CommRing
set_option quotPrecheck false
set_option maxHeartbeats 1500000
attribute [local irreducible] VertexImage.template VertexImage.segments PhysicalScanData.physical TerminalProgram.workers
  BlockSchedule.Templates.execute CursorNetwork.cursorState CursorBounds.wordBits stateScanPhase
  VertexImage.placement
open private scanWords scanMachine capacity from OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

variable {k : Type} [Field k] {S : BlockSchedule k} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {model : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    {data : D.ScalarData B hn model} {u : PairExponents B.growthConstant} {V : D.VirtualPairs B u hn C}
    [NeZero (virtualBits D.addressFactor n)]
    {ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)} {i : D.groupIndices n} {μ : D.pairNom n C}
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
local notation "ref" => RefreshVertex.refreshSegment B (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride names
local notation "code" => VertexImage.segments geo TerminalRootGather.segment LeafRole.segment shr ref
local notation "W" => TerminalProgram.workers shape B.recordLimit code

local notation "arc" => scan.arc z
local notation "parsers" => scan.sites z

variable (q lo before layout clock headerFit below agree) {power scanRate : ℕ}
  (R : RatedSelection (mem := mem) scan z names rowBase counter grammar cap pub q lo before layout clock headerFit
    below agree power scanRate)
  (counterEnd : counter+grammar+g ≤ (header pub).val)

local notation "visit₀" => R.selectedSites scan z names rowBase counter grammar cap pub q lo before layout
  clock headerFit below agree counterEnd

local notation "branch₀" => R.branch scan z names rowBase counter grammar cap pub q lo before layout
  clock headerFit below agree counterEnd

/-- Deposit the canonical jobs into each grammar or motif counter word. -/
theorem RatedSelection.deposits (x : TerminalData (arc) (parsers))
    (ptr : RowPointers (selectedChain (V := V) (M := model) z))
    (leaf : V.scanState.network.Site → ℕ × ℕ) (input : Memory w)
    (initial : ∀ j : Fin (grammar+g), ((visit₀) x.arcs).sourceMem (counter+j.val) = input (counter+j.val))
    (j : Fin (grammar+g)) :
    ((branch₀).vertexPaths x.arcs x.choices).val.memory (counter+j.val) =
      Counters.visit counter grammar (fun v k => scan.siteTotals z x ptr leaf v (names.symm k))
        (List.ofFn ord) input (counter+j.val) := by
  have cell := TerminalFootprint.below (header pub) (by omega)
    (show counter+j.val < (header pub).val from (Nat.add_lt_add_left j.isLt counter).trans_le
      (Nat.add_assoc counter grammar g ▸ counterEnd))
  let chain := selectedChain (V := V) (M := model) z
  let readers := selectedParsers B κ hf T le_rfl V.scanState z
  exact selectedTerminalBranch_deposited (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10
    sl rfl 0 rfl (fun _ => 0) 0 bitFit (parsers) ord names.symm shape B.recordLimit pub q lo before
    layout clock headerFit below agree counter grammar (visit₀) x
    (chainTrees chain readers ptr (fun v => leafTree (leaf v))) (vertexJobs chain readers ptr scan.leafSites leaf)
    (vertexJobs_spec chain readers ptr scan.leafSites leaf) input (counter+j.val) cell (initial j)

/-- Reindexing the worker tables preserves every physical deposit. -/
theorem RatedSelection.deposits_reindex {current : TerminalLink.Stage → LiveProgram.PairTable}
    (same : W = current) (x : TerminalData (arc) (parsers))
    (ptr : RowPointers (selectedChain (V := V) (M := model) z))
    (leaf : V.scanState.network.Site → ℕ × ℕ) (input : Memory w)
    (initial : ∀ j : Fin (grammar+g), ((visit₀) x.arcs).sourceMem (counter+j.val) = input (counter+j.val))
    (j : Fin (grammar+g)) :
    (((branch₀).reindexWorkers same).vertexPaths x.arcs x.choices).val.memory (counter+j.val) =
      Counters.visit counter grammar (fun v k => scan.siteTotals z x ptr leaf v (names.symm k))
        (List.ofFn ord) input (counter+j.val) := by
  exact (congrFun ((branch₀).reindex_vertexMemory same x) _).trans
    (R.deposits scan z names rowBase counter grammar cap pub q lo before layout clock headerFit below
      agree counterEnd x ptr leaf input initial j)

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
