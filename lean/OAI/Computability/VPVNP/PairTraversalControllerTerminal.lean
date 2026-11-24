import OAI.Computability.VPVNP.PairTraversalControllerRun
import OAI.Computability.VPVNP.PairSimulationTerminalProgram
import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild

/-!
# Entering the native traversal controller in the terminal machine

Stage two starts its local ordinal at zero. Its ordinary worker reports are
lifted to the terminal instruction image, which saves the returned ordinal
on intermediate calls and hands off to the shared-bit phase on acceptance.
All row, tag, input, and final-bit words agree with the selected native arena.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM CompressorRecords TerminalLink
open LiveProgram (PairTable)
open scoped Fin.CommRing

variable {w : ℕ}

/-- Lift the verified closed traversal segment into the five-stage image.
The final agreement applies to every word except the two terminal controls. -/
theorem linked_stage (workers : Stage → PairTable) (pub : Fin 11 → Word w)
    (bank : workers Stage.traversalRows = ⟨Native.P, R, Native.table⟩)
    {src phy final : Memory w} {fuel outer calls probes : ℕ} {out : List (Report w)}
    (segment : Segment (Native.machine pub).program fuel (some 0) none src final calls probes out)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog out))
    (room : fuel + 30 ≤ outer) (wide : 32 ≤ 2 ^ w)
    (valid : (Entry.resume Stage.traversalRows (0 : Word w)).Valid (header pub) phy)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy) :
    let entry := Entry.resume Stage.traversalRows (0 : Word w)
    let bs : List (List Bool) := List.replicate calls []
    let physical := after phy (eventLog (stageReports (header pub) entry out))
    StageRun workers pub outer entry src phy bs out ∧
      Phase workers pub outer entry phy bs (stageLogs entry out) physical ∧
      SourceTransport.Agree (workerCell (header pub)) final physical := by
  intro entry bs physical
  have sourceRun : runSegment (source workers entry.stage pub) fuel (some entry.state) src bs =
      some out := by
    change runSegment (source workers Stage.traversalRows pub) fuel (some 0) src bs = some out
    unfold source
    rw [bank]
    exact segment.run
  have h := closed_stage_run workers pub fuel outer entry src phy bs out wide room valid agree reads
    sourceRun segment.endAt
  exact ⟨h, closed_phase workers pub fuel outer entry src phy bs out room agree reads sourceRun
    segment.endAt, segment.memory ▸ h.agree⟩

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
