import OAI.Computability.VPVNP.LiveCompressedPairReindex
import OAI.Computability.VPVNP.PairSimulationTerminalDataPaths
import OAI.Computability.VPVNP.PairSimulationTerminalProgram

/-!
# The compressed pair with the five-stage terminal table

For each selected descriptor branch, the genuine terminal program runs on
the online stage's transferred memory. Its deterministic setup, shared-bit
scan and per-site witnesses give a single branch-indexed equivalence for the
complete eleven-word pair table and its actual dense-counter readback.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM CompressorRecords CompressorRecords.Schedule PairSimulation LocalHistory NetworkKernel
open PairStages.Group.CompressedPaths

variable {d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
variable (shape : DescriptorSpace.Shape) (limit : ℕ) (segments : VertexImage.Part → VertexImage.Segment)
variable (G : PairStages.Group) (B n base : ℕ) (m : Memory G.w)

/-- The outer table already separates enough word values for all 32
terminal-header offsets. -/
theorem terminal_tag_fits (G : PairStages.Group) : 32 ≤ 2^G.w := by
  by_cases h : 5 ≤ G.w
  · exact (by decide : 32 ≤ 2^5).trans (Nat.pow_le_pow_right (by decide) h)
  · have small := Nat.pow_le_pow_right (n := 2) (by decide) (show G.w ≤ 4 by omega)
    have hf : 21 ≤ 2^G.w := G.tagFit
    norm_num at small
    omega

/-- Both nested dispatches leave the private clock needed for the shared
bit phase, including its bounded source-to-physical replay. -/
theorem terminal_clock_fits (G : PairStages.Group) (hc : 154 ≤ G.clock) :
    54 ≤ clockAt (publicWords G) (fuel G) Stage.terminal := by
  have outer : (LiveStageLink.dispatchEvents G.addr LiveProgram.Stage.pair).length ≤ 44 := by
    simp only [LiveStageLink.dispatchEvents,List.length_cons,List.length_replicate]
    decide
  have inner : (LiveStageLink.dispatchEvents (PairTag.address (publicWords G)) Stage.terminal).length = 22 := by
    simp only [LiveStageLink.dispatchEvents,List.length_cons,List.length_replicate]
    decide
  change 54 ≤ (G.clock - (LiveStageLink.dispatchEvents G.addr LiveProgram.Stage.pair).length) - 5 -
    (LiveStageLink.dispatchEvents (PairTag.address (publicWords G)) Stage.terminal).length
  omega

/-- The static five-worker program for the particular fixed pair. -/
noncomputable abbrev terminalBody := TerminalProgram.table shape limit segments

variable {b plan shape limit segments G B n base m}
variable (S : PhysicalStages b plan (terminalBody shape limit segments) G B n base m)

local notation "operands" => publicWords G
local notation "clock" => fuel G
local notation "finalTable" => terminalBody shape limit segments
local notation "startup" => cursorStartupLogs b operands B n base m initial phases d
local notation "entry" => after m (eventLog startup)

variable {Z I : Type*} (descriptorPaths :
  Z ≃ StagePaths b plan (terminalBody shape limit segments) (publicWords G) (fuel G) Stage.online
    (after m (eventLog (cursorStartupLogs b (publicWords G) B n base m initial phases d))))

/-- A selected terminal execution uses three forced metadata stages, then a
shared arc phase and a vertex phase for that specific arc assignment. -/
structure TerminalBranchData {w : ℕ} (workers : TerminalLink.Stage → PairTable) (ports : Fin 11 → Word w)
    (f : ℕ) (mem : Memory w) {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}
    {N : Network} (sc : ScanPhase N) (P : SiteParsers κ N) where
  /-- The deterministic terminal prefix on the selected online path's post-memory. -/
  setup : TerminalLink.QuietPrefix workers ports f mem
  /-- The equivalence between the mathematical shared-wire scan paths and the terminal prefix's
  native bit paths. -/
  bitPaths : sc.Path ≃ setup.BitPaths
  /-- For each shared-bit path, the equivalence between the sites' witness choices and the
  native vertex paths on that assignment. -/
  vertexPaths : ∀ a : sc.Path,
    (∀ v, (P.witnesses v (WireTensor.edgeAssignment N.src N.dst (sc.payload a) v)).Choice) ≃
      setup.VertexPaths (bitPaths a)

attribute [local irreducible] regs components TerminalProgram.workers

/-- The terminal setup, shared-bit paths, and vertex-path evidence specialized to one selected
descriptor path. -/
noncomputable abbrev TerminalBranch {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}
    {N : Network} (sc : ScanPhase N) (P : SiteParsers κ N) (z : Z) :=
  TerminalBranchData (TerminalProgram.workers shape limit segments) (publicWords G)
    (clockAt (publicWords G) (fuel G) Stage.terminal) (onlinePost (descriptorPaths z)) sc P

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N : Z → Network}
variable {sc : (z : Z) → ScanPhase (N z)} {sites : (z : Z) → SiteParsers κ (N z)}
variable (tagFits : 32 ≤ 2^G.w) (clockFits : 26 ≤ clockAt (publicWords G) (fuel G) Stage.terminal)
variable (branches : ∀ z : Z, TerminalBranch descriptorPaths (sc z) (sites z) z)
variable (emit : (Σ z : Z, TerminalData (sc z) (sites z)) ≃ I)

/-- Identify the mathematical terminal data of a descriptor choice with accepted executions of
its actual terminal program. -/
noncomputable def terminalPaths (z : Z) :
    TerminalData (sc z) (sites z) ≃
      ActualPaths (original b plan finalTable operands Stage.terminal) (clockAt operands clock Stage.terminal)
        0 (onlinePost (descriptorPaths z)) (fun _ => True) :=
  (branches z).setup.dataPaths (branches z).bitPaths (branches z).vertexPaths tagFits clockFits (fun _ => True)
    (fun _ => trivial)

/-- Combine startup, descriptor choices, and terminal witnesses to identify the full emitted
index with a raw accepted pair path. -/
noncomputable def PhysicalStages.reindexTerminal : I ≃ Raw G m :=
  S.reindex emit descriptorPaths (terminalPaths descriptorPaths tagFits clockFits branches)

theorem PhysicalStages.reindexTerminal_tapes (z : Z) (x : TerminalData (sc z) (sites z)) :
    (S.reindexTerminal descriptorPaths tagFits clockFits branches emit (emit ⟨z,x⟩)).val =
      List.replicate 8 [] ++ ((descriptorPaths z).val ++
        ((branches z).setup.trace ((branches z).bitPaths x.arcs) ((branches z).vertexPaths x.arcs x.choices)).choices) := by
  rw [reindexTerminal,reindex_tape]
  rfl

theorem PhysicalStages.reindexTerminal_logs (z : Z) (x : TerminalData (sc z) (sites z)) :
    reports (S.reindexTerminal descriptorPaths tagFits clockFits branches emit (emit ⟨z,x⟩)) =
      startup ++ (onlineReports (descriptorPaths z) ++
        (TerminalLink.reports (TerminalLink.header operands)
          ((branches z).setup.trace ((branches z).bitPaths x.arcs) ((branches z).vertexPaths x.arcs x.choices)).logs).map
            (report operands Stage.terminal)) := by
  rw [reindexTerminal,reindex_logs]
  congr 3
  exact TerminalLink.QuietPrefix.dataPaths_logs ..

theorem PhysicalStages.reindexTerminal_after (z : Z) (x : TerminalData (sc z) (sites z)) :
    after m (eventLog (reports (S.reindexTerminal descriptorPaths tagFits clockFits branches emit (emit ⟨z,x⟩)))) =
      ((branches z).vertexPaths x.arcs x.choices).val.memory := by
  rw [reindexTerminal,reindex_after]
  exact TerminalLink.QuietPrefix.dataPaths_after ..

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
