import OAI.Computability.VPVNP.PairVertexRatedSelection
import OAI.Computability.VPVNP.LiveSelectedTerminalFrame
import OAI.Computability.VPVNP.PairTerminalQuietHandoff

/-! # Physical frame of the rated terminal vertex execution -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM PrivateRAM CompressorRecords SourceTransport
open PairSimulation LocalHistory NetworkKernel LiveProgram CompressedPair TerminalLink CutSchedule ExponentTrace
open scoped Fin.CommRing
set_option quotPrecheck false
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

variable (q : QuietPrefix (TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit
    (TerminalProgram.nativeSegments B D.constants D.numerator D.denominator names)) pub cap mem)
  (lo : ℕ) (before : Memory (CursorBounds.wordBits D.addressFactor n))
  (layout : FinalBits.Worker.Layout pub before lo ((V.selection (M := model)).finalState z).totalWidth)
  (clock : 54 ≤ cap) (headerFit : (header pub).val+32 ≤ 2^(CursorBounds.wordBits D.addressFactor n))
  (below : lo+((V.selection (M := model)).finalState z).totalWidth ≤ (header pub).val)
  (agree : Agree (workerCell (header pub)) before q.traversalRows.val.memory)

variable {power scanRate : ℕ}
  (R : RatedSelection scan z names rowBase counter grammar cap pub q lo before layout clock headerFit
    below agree power scanRate)
  (counterEnd : counter+grammar+g ≤ (header pub).val)


local notation "parsers" => scan.sites z

include R counterEnd in
/-- The concrete rated rows preserve every earlier address outside their
histogram on all reachable bursts. The conclusion is stated on the actual
packed worker bank used by the pair linker. -/
theorem RatedSelection.branch_frames {packed : TerminalLink.Stage → PairTable}
    (bank : (W) = packed)
    (low : (pub 2).val ≤ lo)
    (prefixFrame : ∀ a < (pub 2).val, ReplayFrame a mem q.reportList)
    (a : ℕ) (beforeWorkspace : a < (pub 2).val)
    (outside : a < counter+grammar ∨ counter+grammar+g ≤ a) :
    PreservesCell (TerminalLink.program packed pub) cap 0 mem a := by
  subst packed
  have wide : 32 ≤ 2^w := by omega
  intro st now tape result reached run
  exact selectedTerminalBranch_word (Y) scanM Fin.castSucc (Function.Embedding.refl _) 0 10 sl rfl
    0 rfl (fun _ => 0) 0 bitFit (parsers) ord names.symm shape B.recordLimit pub q lo before layout
    clock headerFit below agree counter grammar (R.selectedSites scan z names rowBase counter grammar cap pub q lo before layout
      clock headerFit below agree counterEnd) a (beforeWorkspace.trans_le low) outside
    (prefixFrame a beforeWorkspace) (q.valid_sharedBits wide) reached run

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
