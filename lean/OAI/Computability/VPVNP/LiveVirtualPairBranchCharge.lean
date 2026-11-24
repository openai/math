import OAI.Computability.VPVNP.LiveVirtualPairBranchClocks
import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.LiveVirtualPairSourceAssembly
import OAI.Computability.VPVNP.LiveCompressedPairBranchCharge

/-! # The physical budget on a selected finite-model pair -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM LiveProgram CompressedPair
open PairStages.Group.CompressedPaths NetworkKernel PairSimulation LocalHistory CompressorRecords ScheduledTrace
open scoped Fin.CommRing
set_option quotPrecheck false
set_option maxHeartbeats 1200000

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
  {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)
  {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
  {c : Constants} {labels : c.motifLabels = Fintype.card B.Entry} {raw site q link base : ℕ}

local notation "grp" => D.executionGroup n ht hf
local notation "ports" => publicWords (grp)
local notation "clk" => fuel (grp)
local notation "boot" => paperBootstrap B u
local notation "A" => BlockProgram.script B
local notation "w" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "P" => initialPositions D.addressFactor n
local notation "L" => BlockProgram.layout B base P T
local notation "rate" => nativePassRate (A) raw * P
local notation "bound" => TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit + 1
local notation "κ" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "sel" => V.selection (M := M)
local notation "lastStage" => terminalBody (L).shape B.recordLimit (paperSegments B u c labels)

attribute [local irreducible] BlockProgram.script BlockProgram.layout CompressedPair.stages CompressedPair.regs
  CompressedPair.components TerminalProgram.workers CursorNetwork.cursorState

variable {m : Memory (wordBits D.addressFactor n)}
    (descriptor : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) c labels base
      (fuel (D.executionGroup n ht hf)) (nativePassRate (BlockProgram.script B) raw * initialPositions D.addressFactor n)
      (publicWords (D.executionGroup n ht hf)) m)
    {arc : (z : (V.selection (M := M)).Choices) → ScanPhase ((V.selection (M := M)).finalState z).network}
    {sites : (z : (V.selection (M := M)).Choices) → SiteParsers (B.compressorValues hn M) ((V.selection (M := M)).finalState z).network}
    (branches : ∀ z : (V.selection (M := M)).Choices, TerminalBranch (b := paperBootstrap B u) (plan := (BlockProgram.script B).plan)
      (shape := (BlockProgram.layout B base (initialPositions D.addressFactor n) (blockCount (u.θ : ℝ) n)).shape)
      (limit := B.recordLimit) (segments := paperSegments B u c labels) (G := D.executionGroup n ht hf)
      (B := D.addressFactor) (n := n) (base := base) (m := m) descriptor.paths (arc z) (sites z) z)

set_option maxHeartbeats 800000 in
/-- The linked online path and terminal phases on the same selected finite-model
assignment give the full resource field of the native group certificate. -/
theorem VirtualPairs.PaperDescriptor.branchCharge
    (h : BranchClocks.{0} B u D.addressFactor boot (A).initial.length (A).block.length raw site q link n)
    (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den)
    (z : (sel).Choices) (x : TerminalData (arc z) (sites z))
    (hq : 1 ≤ q)
    (prefixRun : Nonempty (PreludeCosts V.scanState ((sel).finalState z) ports ((branches z).chosenTrace x)
      S.steps B.recordLimit T bound))
    (suffixRun : ∃ (bitMemory last : Memory (grp).w) (bits : Fin ((sel).finalState z).totalWidth → Bool)
        (vertex : ((sel).finalState z).network.Site → Report (grp).w),
      ((branches z).chosenTrace x).sharedBits.logs.map Prod.snd = FinalBits.Worker.reports ports 0 bitMemory bits ∧
      ((branches z).chosenTrace x).vertices.logs.map Prod.snd = (List.ofFn fun i => vertex ((siteOrder ((sel).finalState z)).entries i)) ++
        [VertexImage.closingReport ports last] ∧
      ∀ v, 1+(vertex v).probes ≤ siteAccesses ((sel).finalState z) (selectedChain (V := V) (M := M) z) site q n v ∧
        (vertex v).events.length+107 ≤ n^45) :
    let rs := branchReports descriptor.paths branches z x
    (∀ r ∈ rs, r.events.length+4 ≤ clk) ∧ 4*RAMBuckets.cost Report.probes rs ≤ 2^(D.geometry n).d*(D.geometry n).H ∧
      ∀ r ∈ rs, 3+r.probes ≤ (D.geometry n).H := by
  intro rs
  obtain ⟨prelude⟩ := prefixRun
  obtain ⟨bitMemory,last,bits,vertex,bitRows,vertexRows,checked⟩ := suffixRun
  have hsizes : 2^(D.geometry n).d = processorCount D.addressFactor n ∧ (D.geometry n).H = liveCapacity u n := by
    rw [paperGeometry_eq D B u num den n]
    exact ⟨rfl,rfl⟩
  obtain ⟨_,clock,active,startup,bootCap,arenaCap⟩ := h.groupCaps (grp) rfl
  have term := V.terminalClock (M := M) h num den z
  have online := V.onlineClock (M := M) h num den descriptor.cursor.interval descriptor.cursorCost descriptor.result (grp) rfl z
  let core := descriptor.cursor.interval.combinedCore descriptor.result.trace descriptor.result.source z
  have framed := (DescriptorPaths.paths_reports descriptor.cursor.interval descriptor.result boot lastStage clk
    descriptor.clock descriptor.slack z).trans core.frame
  apply branchReports_caps descriptor.paths branches z x V.scanState ((sel).finalState z) (selectedChain (V := V) (M := M) z)
    (2^(D.geometry n).d) (D.geometry n).H S.steps T site q bound (hsizes.1.symm ▸ h.processors)
    (hsizes.2.symm ▸ h.capacity) clock descriptor.init (hsizes.2.symm ▸ h.startBurst) startup
    core.logs framed online.2 online.1 prelude (hsizes.2.symm ▸ bootCap) (hsizes.2.symm ▸ arenaCap) bitMemory last bits
    bitRows vertex vertexRows hq h.blocks (fun v => ⟨(checked v).1,(checked v).2.trans active⟩) term.2 term.1

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
