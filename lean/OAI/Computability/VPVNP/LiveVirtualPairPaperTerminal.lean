import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.LiveVirtualPairNativeAssembly
import OAI.Computability.VPVNP.LiveTerminalReachableFrame

/-! # The fixed pair's terminal execution on the selected descriptor

Every selected branch runs against the post-memory of the actual online
calendar. The terminal block must account for the sparse counter readback,
the path caps, and preservation of both the pair tag and the live header
even on branches whose next vertex rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.CompressedPaths CompressedPair
open PairSimulation PairSimulation.LocalHistory NetworkKernel CompressorRecords CompressorRecords.Schedule

set_option quotPrecheck false
open scoped Fin.CommRing

attribute [local irreducible] CompressedPair.stages CompressedPair.regs CompressedPair.components TerminalProgram.workers

variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
    {K : Type} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
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
local notation "f" => B.compressorValues hn M
local notation "hf₀" => B.compressorValues_solution hn M
local notation "T" => blockCount (u.θ : ℝ) n
local notation "positions" => initialPositions D.addressFactor n
local notation "L" => BlockProgram.layout B ws positions T
local notation "boot" => paperBootstrap B u
local notation "script" => BlockProgram.script B
local notation "parts" => paperSegments B u D.constants hg
local notation "lastStage" => TerminalProgram.table (L).shape B.recordLimit parts
local notation "termProgram" => original boot (script).plan lastStage ports CompressedPair.Stage.terminal
local notation "termClock" => clockAt ports clk CompressedPair.Stage.terminal

variable (rate : ℕ)
variable (Y : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) D.constants hg
  ((Layout.pairWorkspace D.constants).eval (D.geometry n)) (fuel (D.executionGroup n ht hf)) rate
  (publicWords (D.executionGroup n ht hf)) (I.branch.copy.memory ()))

/-- Five-block witnesses and the four physical assertions required of their
native traces. Each component type is specialized to the selected descriptor. -/
structure TerminalEvidence (Branches Pointers Leaves : Type*) (Tag Header : Prop)
    (Deposits : Branches → Pointers → Leaves → Prop) (Caps : Branches → Prop) where
  /-- The complete five-stage execution on each selected descriptor branch. -/
  branches : Branches
  /-- Addresses of the compressed placement tree at each visited level. -/
  ptr : Pointers
  /-- Addresses of the cursor vertices at the input level. -/
  leaf : Leaves
  tag : Tag
  header : Header
  deposits : Deposits branches ptr leaf
  caps : Caps branches

/-- The native five-block witness for the actual selected calendar, together
with its site jobs and physical readbacks. -/
abbrev VirtualPairs.PaperTerminal :=
  TerminalEvidence
    (∀ z : (sel).Choices, TerminalBranch (b := boot) (plan := (script).plan)
      (shape := (L).shape) (limit := B.recordLimit) (segments := parts) (G := grp)
      (B := D.addressFactor) (n := n) (base := ws) (m := mem) Y.paths (A.arc z) (A.sites z) z)
    (∀ z : (sel).Choices, RowPointers (selectedChain (V := V) (M := M) z))
    ((V.scanState).network.Site → ℕ × ℕ)
    (∀ z, PreservesCell termProgram termClock 0 (onlinePost (Y.paths z)) (PairTag.address ports).val)
    (∀ z a, a < Auxiliary.tableBase grp → PreservesCell termProgram termClock 0 (onlinePost (Y.paths z)) a)
    (fun branches ptr leaf => ∀ z (x : TerminalData (A.arc z) (A.sites z)) (j : Fin (labelCount grp)),
      ((branches z).vertexPaths x.arcs x.choices).val.memory (Auxiliary.counterBase grp+j.val) =
        (Counters.visit (Auxiliary.counterBase grp) (Auxiliary.histLength grp)
          (fun v k => A.siteTotals z x (ptr z) leaf v (physicalMotifOrder hg k))
          (List.ofFn (siteOrder ((sel).finalState z)).entries) mem) (Auxiliary.counterBase grp+j.val))
    (fun branches => ∀ z (x : TerminalData (A.arc z) (A.sites z)),
      let rs := branchReports Y.paths branches z x
      (∀ r ∈ rs, r.events.length+4 ≤ clk) ∧ 4*RAMBuckets.cost Report.probes rs ≤ 2^(D.geometry n).d*(D.geometry n).H ∧
        ∀ r ∈ rs, 3+r.probes ≤ (D.geometry n).H)

set_option maxHeartbeats 1200000 in
/-- The concrete descriptor result and its selected native terminal blocks
supply every premise of the prepared pair's execution certificate. -/
noncomputable def VirtualPairs.nativeRunsOfPaperTerminal
    (fixed : D.pair = paperTable B u D.constants hg)
    (workspace : ws < 2^(D.geometry n).w)
    (setup : TransferredStartup.Runs (bootstrapRows boot (script).initial.length (script).block.length) (script).size
      (startupLayout boot (script).initial.length (script).block.length D.addressFactor n ws)
      D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps ports (PairTag.address ports) mem)
    (Q : V.PaperTerminal data W P hC hg cut I A rate Y) : V.nativeRuns data fit W P hC hg cut I := by
  have base : (ports 2).val = ws := Nat.mod_eq_of_lt workspace
  have lt := tag_before_workspace D.constants (D.geometry n)
  have tag : (PairTag.address ports).val < ws := by
    rw [tag_address]
    change (Layout.oldState D.constants).eval (D.geometry n) % 2^(D.geometry n).w < ws
    rw [Nat.mod_eq_of_lt (lt.trans workspace)]
    exact lt
  have below : (PairTag.address ports).val < (ports 2).val+6 := by rw [base]; omega
  have space (a : ℕ) (ha : a < Auxiliary.tableBase grp) : a < (ports 2).val+6 := by
    have upper := (Auxiliary.geometry_order grp).2.2.1
    have old : Auxiliary.tableBase grp ≤ (Layout.oldState D.constants).eval (D.geometry n) := by
      change Auxiliary.tableBase grp ≤ Auxiliary.counterBase grp + D.constants.labels.eval (D.geometry n)
      omega
    rw [base]
    omega
  let tagFrame (p : StagePaths boot (script).plan lastStage ports clk CompressedPair.Stage.online
      (after mem (eventLog (cursorStartupLogs boot ports D.addressFactor n ws mem (script).initial.length
        (script).block.length (script).size)))) :=
    Protected.ofPreservesCell (b := boot) (plan := (script).plan) (last := lastStage) (pub := ports)
      (clock := clk) (s := CompressedPair.Stage.terminal) (m := onlinePost p) (by
        obtain ⟨z,rfl⟩ := Y.paths.surjective p
        exact Q.tag z)
  let physical : PhysicalStages boot (script).plan lastStage grp D.addressFactor n ws mem :=
    { body := by change D.pair = _; rw [fixed,paper_terminal_rows]; rfl
      enough := by
        have enough := terminal_clock_fits grp W.clock
        unfold CompressedPair.clockAt at enough
        omega
      init := Y.init
      onlineFrame := Y.protectedOnline below
      terminalFrame := tagFrame }
  apply V.nativeRunsOfTerminal data fit W P hC hg cut I A physical Y.paths Q.branches setup workspace
    (fun a ha => Y.online_word below a (space a ha)) _ Q.ptr Q.leaf Q.deposits Q.caps
  intro a ha p
  obtain ⟨z,rfl⟩ := Y.paths.surjective p
  exact Protected.ofPreservesCell_word (Q.tag z) (Q.header z a ha)

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
