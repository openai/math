import OAI.Computability.VPVNP.FixedPaperPairRuns
import OAI.Computability.VPVNP.LiveVirtualPairQuietPrelude
import OAI.Computability.VPVNP.LiveVirtualPairVertexCounters
import OAI.Computability.VPVNP.LiveRatedVertexDeposits
import OAI.Computability.VPVNP.LiveRatedTerminalFrames
import OAI.Computability.VPVNP.LiveVirtualPairBranchCharge
import OAI.Computability.VPVNP.LiveTerminalWorkerTransport
import OAI.Computability.VPVNP.LiveRatedArcMemory
import OAI.Computability.VPVNP.LiveRatedRowCharges

/-! # Assembling the actual selected sites into the fixed terminal program

The shared-bit readback, the chronological low-word frame, and the rated
local vertex executions all use one quiet prefix. Transport to the packed
runtime directory preserves the reports and final memory. The two DFS
pointer functions here are the ones used by the physical placement trees.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair LocalCount
open LabelEvaluator CompressorRecords ScheduledTrace DescriptorSpace
open PairStages PairStages.Group PairStages.Group.CompressedPaths SourceTransport
open PairSimulation LocalHistory NetworkKernel TraversalRows TerminalLink
open scoped Fin.CommRing

set_option quotPrecheck false
set_option maxHeartbeats 1400000
/-- Transfer the complete reached-state predicate across the inner table's
final lookup. This also transfers the native configuration type indexed by
the register and program-counter counts of that row. -/
private theorem finalRowFrame {d initial phases w : ℕ} {C : Schedule.Catalog d}
    (boot : Bootstrap) (plan : Schedule.Online.Config C initial phases)
    (shape : DescriptorSpace.Shape) (limit : ℕ) (parts : VertexImage.Part → VertexImage.Segment)
    (ports : Fin 11 → Word w) (clock : ℕ) (mem : Memory w) (a : ℕ) :
    PreservesCell (TerminalLink.program (TerminalProgram.workers shape limit parts) ports)
        clock 0 mem a →
      PreservesCell (original boot plan (TerminalProgram.table shape limit parts) ports
        CompressedPair.Stage.terminal) clock 0 mem a := fun h => @h

attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs CompressedPair.components TerminalProgram.workers paperTable
  BlockSchedule.Templates.execute CursorBounds.virtualBits CursorBounds.wordBits
  VertexImage.template VertexImage.segments PhysicalScanData.physical stateScanPhase
  PhaseRecipe.Expr.slots DescriptorHeads.publisher BlockProgram.geometry BlockProgram.allocationShape

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (u : PairExponents B.growthConstant) (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry)
  (prog : UniversalMachine.Program) (addr : ℕ) (positive : 1 ≤ addr)
local notation "D" => paperProgram B u c labels prog addr positive
variable {n : ℕ} {hn : 2 ≤ n} {ht : 21 ≤ 2^((paperProgram B u c labels prog addr positive).geometry n).w} {hc : 44 ≤ n^10000}
  {p : Nat.Primes} {M : Model p (B.compressorDegree n) (B.compressorEquations hn c.circuitExponent)}
  (data : (paperProgram B u c labels prog addr positive).ScalarData B hn M) (V : (paperProgram B u c labels prog addr positive).VirtualPairs B u hn c.circuitExponent)
  [NeZero (virtualBits ((paperProgram B u c labels prog addr positive).addressFactor) n)]
local notation "G" => (paperProgram B u c labels prog addr positive).executionGroup n ht hc
variable (W : Conditions ((paperProgram B u c labels prog addr positive).executionGroup n ht hc) (2^((paperProgram B u c labels prog addr positive).geometry n).d) ((paperProgram B u c labels prog addr positive).geometry n).H)
  (P : PairStageConditions ((paperProgram B u c labels prog addr positive).executionGroup n ht hc) (2^((paperProgram B u c labels prog addr positive).geometry n).d) ((paperProgram B u c labels prog addr positive).geometry n).H)
  (cut : 1+B.denseCount n c.circuitExponent*(paperProgram B u c labels prog addr positive).counterWidth n ≤ n^c.deltaPower)
  (I : VirtualPairs.PhysicalInput data W P rfl labels cut)
variable (A : CanonicalScan data V (VirtualPairs.exterior data W P rfl labels cut I)
  (VirtualPairs.modelIndex data W P rfl labels cut I) (physicalNomination rfl I.μ))

local notation "script" => BlockProgram.script B
local notation "f" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "sel" => V.selection (M := M)
local notation "T" => blockCount (u.θ : ℝ) n
local notation "ws" => PublicExpr.eval ((D).geometry n) (Layout.pairWorkspace c)
local notation "positions" => initialPositions addr n
local notation "L" => BlockProgram.layout B ws positions T
local notation "rowBase" => endAddress L
local notation "wire" z => rowBase + words B.recordLimit (selectedLayers B f ok T le_rfl V.scanState z)
local notation "ports" => publicWords (G)
local notation "clk" => fuel (G)
local notation "cap" => CompressedPair.clockAt ports clk CompressedPair.Stage.terminal
local notation "names" => entryOrdinal B c labels
local notation "parts" => paperSegments B u c labels
local notation "bank" => TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit parts
local notation "packed" => TerminalProgram.workers (L).shape B.recordLimit parts
local notation "counter" => Auxiliary.counterBase (G)
local notation "grammar" => Auxiliary.histLength (G)
local notation "input" => I.branch.copy.memory ()
local notation "boot" => paperBootstrap B u

variable (raw scanRate link : ℕ)
local notation "rate" => nativePassRate script raw * positions
local notation "site" => VertexReportBudget.coefficient S.baseDegree (Fintype.card B.Entry) 6 scanRate 0 0
local notation "bootCost" => TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit+1

variable (Y : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) c labels
  ((Layout.pairWorkspace c).eval ((paperProgram B u c labels prog addr positive).geometry n)) (fuel ((paperProgram B u c labels prog addr positive).executionGroup n ht hc))
  (nativePassRate (BlockProgram.script B) raw * initialPositions addr n)
  (publicWords ((paperProgram B u c labels prog addr positive).executionGroup n ht hc)) (I.branch.copy.memory ()))

/-- The site constructor consumes the actual post-scan memory at the true
compressed source clock. -/
abbrev RatedAt (z : (sel).Choices) (q : QuietPrefix bank ports cap (onlinePost (Y.paths z)))
    (ready : Y.QuietData z q) : Prop :=
  RatedSelection A z names rowBase counter grammar cap ports q (wire z) q.traversalRows.val.memory
    ready.layout ready.clock ready.headerFit ready.below (fun _ _ => rfl) 1 scanRate

/-- Each mathematical branch has a physical quiet prefix with its complete
per-report footprint and the certified native ordinal executions on it. -/
abbrev RatedBranchesAt : Prop :=
  ∀ z : (sel).Choices, ∃ q : QuietPrefix bank ports cap (onlinePost (Y.paths z)),
    ∃ ready : Y.QuietData z q, RatedAt B u c labels prog addr positive data V W P cut I A raw scanRate Y z q ready ∧
      ∀ a < (ports 2).val, ReplayFrame a (onlinePost (Y.paths z)) q.reportList

local notation "ptr" z => chainPointers B.recordLimit (selectedChain (V := V) (M := M) z)
  (branchOrders (sel) (B.records f ok T le_rfl V.scanState) z)
  (TraversalRows.address B.recordLimit rowBase (siteOrder V.scanState).length)
local notation "leaf" => sitePointers B.recordLimit rowBase (siteOrder V.scanState)

set_option maxHeartbeats 350000 in
/-- The rated rows on the real selected memory produce all fields of the
paper terminal certificate, including the linked total and per-call caps. -/
theorem paperTerminalOfRated_exists
    (setup : TransferredStartup.Runs (bootstrapRows boot (script).initial.length (script).block.length) (script).size
      (startupLayout boot (script).initial.length (script).block.length addr n ws) addr n
      (S.degreeExponent 0) S.laneBits S.steps ports (PairTag.address ports) input)
    (workspace : ws < 2^((D).geometry n).w)
    (rows : RatedBranchesAt B u c labels prog addr positive data V W P cut I A raw scanRate Y)
    (h : BranchClocks.{0} B u addr boot (script).initial.length (script).block.length raw site 1 link n)
    (large : 2048 ≤ n) (degree : S.baseDegree ≤ n) (labelsFit : Fintype.card B.Entry ≤ n)
    (width : ∀ z : (sel).Choices, ((sel).finalState z).maxWireWidth ≤ n)
    (depth : ∀ (z : (sel).Choices) v, (selectedChain (V := V) (M := M) z).occurrences (fun _ => 1) v ≤ n)
    (prefixCosts : ∀ (z : (sel).Choices) (t : FiveTrace packed ports cap (onlinePost (Y.paths z))),
      Nonempty (PreludeCosts V.scanState ((sel).finalState z) ports t S.steps B.recordLimit T bootCost)) :
    Nonempty (V.PaperTerminal data W P rfl labels cut I A rate Y) := by
  classical
  constructor
  let q z := (rows z).choose
  let ready z := (rows z).choose_spec.choose
  let R z := (rows z).choose_spec.choose_spec.1
  have replay z := (rows z).choose_spec.choose_spec.2
  have bankEq : bank = packed := (TerminalLayout.packed_workers B ws positions T parts).symm
  have numeric := terminal_protected_addresses (G) (ports 2).val workspace le_rfl
  have counterEnd z : counter+grammar+c.motifLabels ≤ (header ports).val :=
    numeric.1.2.le.trans ((numeric.1.1.trans_le (ready z).low).le.trans
      ((Nat.le_add_right (wire z) _).trans (ready z).below))
  let rawBranch z := (R z).branch A z names rowBase counter grammar cap ports (q z) (wire z)
    (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
    (fun _ _ => rfl) (counterEnd z)
  let branches z := (rawBranch z).reindexWorkers bankEq
  refine ⟨branches,(fun z => ptr z),leaf,?_,?_,?_,?_⟩
  · intro z
    apply finalRowFrame boot (script).plan (L).shape B.recordLimit parts ports cap (onlinePost (Y.paths z))
    intro st now tape out reached run
    exact (R z).branch_frames A z names rowBase counter grammar cap ports (q z) (wire z)
      (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
      (fun _ _ => rfl) (counterEnd z) bankEq (ready z).low (replay z) _ numeric.1.1 (.inr numeric.1.2.le) reached run
  · intro z a ha
    apply finalRowFrame boot (script).plan (L).shape B.recordLimit parts ports cap (onlinePost (Y.paths z))
    intro st now tape out reached run
    obtain ⟨low,outside⟩ := numeric.2 a ha
    exact (R z).branch_frames A z names rowBase counter grammar cap ports (q z) (wire z)
      (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
      (fun _ _ => rfl) (counterEnd z) bankEq (ready z).low (replay z) a low (.inl outside) reached run
  · intro z x j
    apply (R z).deposits_reindex A z names rowBase counter grammar cap ports (q z) (wire z)
      (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
      (fun _ _ => rfl) (counterEnd z) bankEq x (ptr z) leaf input _ j
    intro j'
    let bitPath := (rawBranch z).bitPaths x.arcs
    have tape := (R z).bitPath_tapes A z names rowBase counter grammar cap ports (q z) (wire z)
      (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
      (fun _ _ => rfl) (counterEnd z) x.arcs
    rw [(R z).sourceMem_eq A z names rowBase counter grammar cap ports (q z) (wire z)
      (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
      (fun _ _ => rfl) (counterEnd z) x.arcs]
    exact Y.vertex_counter_initial data V W P rfl labels cut I rate z setup workspace
      ((ready z).entry _ bitPath tape).1 j'
  · intro z x
    exact Y.branchCharge (arc := A.arc) (sites := A.sites) V branches h rfl rfl z x (by decide)
      (prefixCosts z ((branches z).chosenTrace x))
      ((R z).chosenRows_packed A z names rowBase counter grammar cap ports (q z) (wire z)
        (q z).traversalRows.val.memory (ready z).layout (ready z).clock (ready z).headerFit (ready z).below
        (fun _ _ => rfl) (counterEnd z) bankEq large degree labelsFit (width z) (depth z) x)

/-- Choose a checked terminal certificate on this descriptor. The existence
theorem supplies the native rows, frames, counter readback and clock bounds. -/
noncomputable def paperTerminalOfRated
    (setup : TransferredStartup.Runs (bootstrapRows boot (script).initial.length (script).block.length) (script).size
      (startupLayout boot (script).initial.length (script).block.length addr n ws) addr n
      (S.degreeExponent 0) S.laneBits S.steps ports (PairTag.address ports) input)
    (workspace : ws < 2^((D).geometry n).w)
    (rows : RatedBranchesAt B u c labels prog addr positive data V W P cut I A raw scanRate Y)
    (h : BranchClocks.{0} B u addr boot (script).initial.length (script).block.length raw site 1 link n)
    (large : 2048 ≤ n) (degree : S.baseDegree ≤ n) (labelsFit : Fintype.card B.Entry ≤ n)
    (width : ∀ z : (sel).Choices, ((sel).finalState z).maxWireWidth ≤ n)
    (depth : ∀ (z : (sel).Choices) v, (selectedChain (V := V) (M := M) z).occurrences (fun _ => 1) v ≤ n)
    (prefixCosts : ∀ (z : (sel).Choices) (t : FiveTrace packed ports cap (onlinePost (Y.paths z))),
      Nonempty (PreludeCosts V.scanState ((sel).finalState z) ports t S.steps B.recordLimit T bootCost)) :
    V.PaperTerminal data W P rfl labels cut I A rate Y :=
  Classical.choice (paperTerminalOfRated_exists B u c labels prog addr positive data V W P cut I A
    raw scanRate link Y setup workspace rows h large degree labelsFit width depth prefixCosts)

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
