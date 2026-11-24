import OAI.Computability.VPVNP.PairSimulationTerminalBlocks
import OAI.Computability.VPVNP.PairTraversalControllerTerminal
import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTraversalControllerSelectedRun

/-!
# Deterministic terminal stages before the shared wire guesses

The first three blocks use the source bootstrap, prefix scan and selected
traversal-controller reports. Each block runs on the physical memory left by
the preceding block. Their only branch strings are empty. The shared-bit
worker starts on the resulting physical memory, with the linked handoff cells
excluded from the equality with the ordinary traversal memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords TerminalLink TerminalPrefix.Linked
open LiveProgram (PairTable)

variable {w a g : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w}
variable {cap fuel : ℕ} {Y : State a g} {inc : IncidenceDirectory w} {starts : Word w}
variable {input : Memory w} {boot : Report w} {prefixRows : List (Report w)}

/-- Compose the native row-construction burst sequence with the actual
bootstrap and final-width scans. Its physical post-memory agrees with the
row and tag construction on every cell available to the shared-bit worker. -/
noncomputable def quietPrefixOfRows
    (start : Start workers pub cap fuel Y inc starts input boot prefixRows)
    (clock₀ : fuel + 30 ≤ cap) (clock₁ : 60 ≤ cap) (wide : 32 ≤ 2 ^ w)
    (rowBank : workers Stage.traversalRows = ⟨_, _, TraversalController.Native.table⟩)
    (limit calls probes : ℕ) (arena : Memory w) (rowReports : List (Report w))
    (clock₂ : TraversalController.callFuel limit + 30 ≤ cap) :
    let src₂ := prefixMemory pub input boot prefixRows
    TraversalController.Segment (TraversalController.Native.machine pub).program
      (TraversalController.callFuel limit) (some 0) none src₂ arena calls probes rowReports →
    SourceTransport.Reads (workerCell (header pub)) (eventLog rowReports) →
    { q : QuietPrefix workers pub cap input //
      q.boot.val.choices = [[]] ∧
      q.prefixRows.val.choices = List.replicate (TerminalPrefix.arcCount Y+1) [] ∧
      q.traversalRows.val.choices = List.replicate calls [] ∧
      q.traversalRows.val.logs = stageLogs (.resume Stage.traversalRows 0) rowReports ∧
      SourceTransport.Agree (workerCell (header pub)) arena q.traversalRows.val.memory ∧
      (Entry.resume Stage.sharedBits (0 : Word w)).Valid
        (header pub) q.traversalRows.val.memory } := by
  intro src₂ rows read
  let src₁ := after input boot.events
  let b₀ : CompletedPhase workers pub cap .initial input :=
    ⟨⟨[[]],[(.initial,boot)],bootMemory pub input boot⟩,
      initial_phase workers pub fuel cap input boot clock₀ start.bootCall start.bootHalt⟩
  have source₁ : runSegment (source workers Stage.prefixRows pub) 30 (some 0) src₁
      (List.replicate (TerminalPrefix.arcCount Y+1) []) = some prefixRows := by
    unfold source
    rw [start.prefixBank]
    exact start.rawScan.native
  have ag₁ : SourceTransport.Agree (workerCell (header pub)) src₁ b₀.val.memory := by
    change SourceTransport.Agree (workerCell (header pub)) (after input boot.events)
      (after input (report (header pub) .initial boot).events)
    simpa only [stageReports,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      using start.boot.agree
  let e₁ := Entry.resume Stage.prefixRows (0 : Word w)
  let e₂ := Entry.resume Stage.traversalRows (0 : Word w)
  let b₁ := completedBlock (workers := workers) (pub := pub) (cap := cap) 30
    e₁ src₁ b₀.val.memory _ prefixRows clock₁ ag₁ start.reads source₁ start.rawScan.halt
  have ag₂ := start.handoff_rows
  obtain ⟨run₂,phase₂,eq₂⟩ := TraversalController.linked_stage workers pub rowBank rows read
    clock₂ wide ag₂.2 (fun _ _ => rfl)
  let b₂ : CompletedPhase workers pub cap e₂ b₁.val.memory :=
    ⟨⟨List.replicate calls [], stageLogs e₂ rowReports,
      after b₁.val.memory (eventLog (stageReports (header pub) e₂ rowReports))⟩,phase₂⟩
  let q : QuietPrefix workers pub cap input :=
    ⟨b₀,b₁,b₂,by simp [b₀],fun _ h => List.eq_of_mem_replicate h,
      fun _ h => List.eq_of_mem_replicate h⟩
  exact ⟨q,rfl,rfl,rfl,rfl,eq₂,run₂.valid _ rfl⟩

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
