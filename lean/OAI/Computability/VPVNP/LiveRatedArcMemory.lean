import OAI.Computability.VPVNP.PairVertexRatedSelection
import OAI.Computability.VPVNP.PairVirtualRootPayload

/-! # Shared wire choices and physical memory of the rated branch -/

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


/-- The physical fourth stage chooses the canonical wire bits, followed
by the required empty closing burst. -/
theorem RatedSelection.bitPath_tapes (x : (arc).Path) :
    (((branch₀).bitPaths x).val).choices = FinalBits.calls (scan.sharedBits z x) ++ [[]] :=
  (PhysicalScanData.physical_choices (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10 sl rfl
    0 rfl (fun _ => 0) 0 bitFit shape B.recordLimit code pub cap before q.traversalRows.val.memory
    lo layout clock headerFit below agree x).trans
      (congrArg (· ++ [[]]) (PhysicalScanData.calls (Y) scanM Fin.castSucc
        (Function.Embedding.refl _) 0 10 sl rfl 0 rfl (fun _ => 0) 0 bitFit x))

/-- The active vertex worker starts on the memory produced by the rated
branch's own completed shared-bit phase. -/
theorem RatedSelection.sourceMem_eq (x : (arc).Path) :
    ((visit₀) x).sourceMem = ((branch₀).bitPaths x).val.memory := rfl

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
