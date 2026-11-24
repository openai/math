import OAI.Computability.VPVNP.PairSimulationTerminalFive
import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild

/-!
# Native phase blocks at the terminal workspace

Three deterministic phases set up the row and role metadata. The following
shared-bit phase changes the memory on which the vertex traversal runs.
The complete block includes the physical reports, supplied choices and
final memory so all three can be used at the next phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram CompressorRecords

variable {w : ℕ} (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)

/-- All completed native blocks for one selected phase at one physical memory. -/
abbrev CompletedPhase (e : Entry w) (m : Memory w) :=
  {x : Block w // Phase workers pub cap e m x.choices x.logs x.memory}

variable {workers pub cap} in
/-- A proved source execution realizes a concrete completed block in the
physical memory, including its dispatch and final transfer. -/
def completedBlock (f : ℕ) (e : Entry w) (src phy : Memory w) (bs : List (List Bool))
    (raws : List (Report w)) (room : f+30 ≤ cap)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog raws))
    (run : runSegment (source workers e.stage pub) f (some e.state) src bs = some raws)
    (halt : endState (some e.state) raws = none) : CompletedPhase workers pub cap e phy :=
  ⟨⟨bs,stageLogs e raws,after phy (eventLog (stageReports (header pub) e raws))⟩,
    closed_phase workers pub f cap e src phy bs raws room agree reads run halt⟩

/-- The first three completed terminal phases in sequence, with each call taking an empty
choice tape and each phase starting in the preceding phase's output memory. -/
structure QuietPrefix (m : Memory w) where
  /-- Completed bootstrap phase starting at the terminal controller's initial entry and
  supplied memory. -/
  boot : CompletedPhase workers pub cap .initial m
  /-- Completed prefix-row phase resumed at state zero in the memory left by bootstrap. -/
  prefixRows : CompletedPhase workers pub cap (.resume Stage.prefixRows 0) boot.val.memory
  /-- Completed traversal-row phase resumed at state zero in the memory left by the prefix-row
  phase. -/
  traversalRows : CompletedPhase workers pub cap (.resume Stage.traversalRows 0) prefixRows.val.memory
  bootQuiet : ∀ b ∈ boot.val.choices, b = []
  prefixQuiet : ∀ b ∈ prefixRows.val.choices, b = []
  traversalQuiet : ∀ b ∈ traversalRows.val.choices, b = []

variable {workers pub cap} {m : Memory w}

/-- Completed shared-bit phase beginning at state zero after the three deterministic terminal
phases. -/
abbrev QuietPrefix.BitPaths (p : QuietPrefix workers pub cap m) :=
  CompletedPhase workers pub cap (.resume Stage.sharedBits 0) p.traversalRows.val.memory

/-- Completed vertex phase beginning at state zero in the memory produced by the given
shared-bit phase. -/
abbrev QuietPrefix.VertexPaths (p : QuietPrefix workers pub cap m) (bits : p.BitPaths) :=
  CompletedPhase workers pub cap (.resume Stage.vertices 0) bits.val.memory

/-- Assemble the bootstrap, prefix-row, traversal-row, shared-bit, and vertex completions into
one certified five-phase execution trace. -/
def QuietPrefix.trace (p : QuietPrefix workers pub cap m) (bits : p.BitPaths) (vertices : p.VertexPaths bits) :
    FiveTrace workers pub cap m :=
  ⟨p.boot.val,p.prefixRows.val,p.traversalRows.val,bits.val,vertices.val,
    p.boot.prop,p.prefixRows.prop,p.traversalRows.prop,bits.prop,vertices.prop⟩

theorem QuietPrefix.trace_choices (p : QuietPrefix workers pub cap m) (bits : p.BitPaths) (vertices : p.VertexPaths bits) :
    (p.trace bits vertices).choices = p.boot.val.choices ++ (p.prefixRows.val.choices ++
      (p.traversalRows.val.choices ++ (bits.val.choices ++ vertices.val.choices))) := rfl

theorem QuietPrefix.trace_logs (p : QuietPrefix workers pub cap m) (bits : p.BitPaths) (vertices : p.VertexPaths bits) :
    (p.trace bits vertices).logs = p.boot.val.logs ++ (p.prefixRows.val.logs ++
      (p.traversalRows.val.logs ++ (bits.val.logs ++ vertices.val.logs))) := rfl

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
