import OAI.Computability.VPVNP.LiveVirtualPairSourceAssembly
import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

/-!
# Instantiating the native source certificate for the chosen finite model

The coefficient counter uses the exterior, pair index and nomination of
this physical group. For each actual descriptor selection, the terminal
vertex jobs update the dense counter bank. Their integer increments recover
the exponents of exactly the canonical virtual occurrence decoded from
the ordinal emission.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.CompressedPaths CompressedPair
open PairSimulation PairSimulation.LocalHistory NetworkKernel CompressorRecords CompressorRecords.Schedule

attribute [local irreducible] CompressedPair.stages CompressedPair.regs CompressedPair.components TerminalProgram.workers

universe v
variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
    {K : Type v} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M) (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C) [NeZero (virtualBits D.addressFactor n)]

local notation "grp" => D.executionGroup n ht hf
variable (W : Conditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (cut : 1+B.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower)
    (I : VirtualPairs.PhysicalInput data W P hC hg cut)
local notation "ext" => VirtualPairs.exterior data W P hC hg cut I
local notation "idx" => VirtualPairs.modelIndex data W P hC hg cut I
local notation "nom" => physicalNomination hC I.μ
local notation "mem" => I.branch.copy.memory ()
local notation "sel" => V.selection (M := M)
local notation "ws" => PublicExpr.eval (D.geometry n) (Layout.pairWorkspace D.constants)
local notation "ports" => publicWords grp
local notation "clk" => fuel grp

variable (A : CanonicalScan data V (VirtualPairs.exterior data W P hC hg cut I)
    (VirtualPairs.modelIndex data W P hC hg cut I) (physicalNomination hC I.μ))
variable {d initial phases : ℕ} {catalog : Catalog d} {b : Bootstrap} {plan : Online.Config catalog initial phases}
    {shape : DescriptorSpace.Shape} {limit : ℕ} {segments : VertexImage.Part → VertexImage.Segment}
local notation "lastStage" => terminalBody shape limit segments
local notation "entry" => after mem (eventLog (cursorStartupLogs b ports D.addressFactor n ws mem initial phases d))
variable (physical : PhysicalStages b plan (terminalBody shape limit segments) (D.executionGroup n ht hf)
    D.addressFactor n ((Layout.pairWorkspace D.constants).eval (D.geometry n)) (I.branch.copy.memory ()))
variable (descriptor : (V.selection (M := M)).Choices ≃ StagePaths b plan (terminalBody shape limit segments)
    (publicWords (D.executionGroup n ht hf)) (fuel (D.executionGroup n ht hf)) CompressedPair.Stage.online
    (after (I.branch.copy.memory ()) (eventLog (cursorStartupLogs b (publicWords (D.executionGroup n ht hf)) D.addressFactor n
      ((Layout.pairWorkspace D.constants).eval (D.geometry n)) (I.branch.copy.memory ()) initial phases d))))
    (branches : ∀ z : (V.selection (M := M)).Choices, TerminalBranch (b := b) (plan := plan)
      (shape := shape) (limit := limit) (segments := segments) (G := D.executionGroup n ht hf) (B := D.addressFactor) (n := n)
      (base := (Layout.pairWorkspace D.constants).eval (D.geometry n)) (m := I.branch.copy.memory ()) descriptor (A.arc z) (A.sites z) z)

set_option maxHeartbeats 1200000 in
/-- A physical descriptor classification and the five actual terminal blocks
supply the native-run certificate. The deposited counters here are the
source's local job counts. The conversion to canonical algebraic exponents
is proved by `CanonicalScan.flush`. -/
noncomputable def VirtualPairs.nativeRunsOfTerminal
    (setup : TransferredStartup.Runs (bootstrapRows b initial phases) d
      (startupLayout b initial phases D.addressFactor n ws) D.addressFactor n b.degreeBits b.lanesPerBlock b.steps
      ports (PairTag.address ports) mem) (workspaceFit : ws < 2^(D.geometry n).w)
    (onlineFrame : ∀ a < Auxiliary.tableBase grp, physical.onlineFrame.word a)
    (terminalFrame : ∀ a < Auxiliary.tableBase grp, ∀ path, (physical.terminalFrame path).word a)
    (ptr : ∀ z : (sel).Choices, RowPointers (selectedChain (V := V) (M := M) z))
    (leaf : (V.scanState).network.Site → ℕ × ℕ)
    (deposited : ∀ z (x : TerminalData (A.arc z) (A.sites z)) (j : Fin (labelCount grp)),
      ((branches z).vertexPaths x.arcs x.choices).val.memory (Auxiliary.counterBase grp+j.val) =
        (Counters.visit (Auxiliary.counterBase grp) (Auxiliary.histLength grp)
          (fun v k => A.siteTotals z x (ptr z) leaf v (physicalMotifOrder hg k))
          (List.ofFn (siteOrder ((sel).finalState z)).entries) mem) (Auxiliary.counterBase grp+j.val))
    (budget : ∀ z (x : TerminalData (A.arc z) (A.sites z)),
      let rs := branchReports descriptor branches z x
      (∀ r ∈ rs, r.events.length+4 ≤ clk) ∧ 4*RAMBuckets.cost Report.probes rs ≤ 2^(D.geometry n).d*(D.geometry n).H ∧
      ∀ r ∈ rs, 3+r.probes ≤ (D.geometry n).H) : V.nativeRuns data fit W P hC hg cut I := by
  apply PhysicalStages.sourceRuns physical (A.encoding fit) (A.emission fit) _ descriptor (terminal_tag_fits grp)
    ((by decide : 26 ≤ 54).trans (terminal_clock_fits grp W.clock)) branches
    (A.ordinals fit) setup rfl workspaceFit I.shadowFit onlineFrame terminalFrame _ budget
  intro z x j
  exact (deposited z x j).trans (congrFun (A.flush fit z x (ptr z) leaf
    (Auxiliary.counterBase grp) (Auxiliary.histLength grp) (physicalMotifOrder hg) mem)
    (Auxiliary.counterBase grp+j.val))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
