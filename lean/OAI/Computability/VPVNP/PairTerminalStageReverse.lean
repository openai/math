import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild

/-!
# Identifying the first two stages of an arbitrary accepting terminal trace

The bootstrap executes once from the original memory. Its empty-tape
execution fixes the entire report even at a different fuel allowance.
The following deterministic prefix is recovered across the two controller
cells, retaining each actual entry tag and the final physical memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram CompressorRecords
open scoped Fin.CommRing

variable {w cap : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w}

/-- On identical starting memory a single accepting empty-tape call determines
the whole stage, including its physical exit. No read footprint is required. -/
theorem Phase.force_oneShot {e m bs ls final} (h : Phase workers pub cap e m bs ls final)
    {f : ℕ} {raw : Report w}
    (run : execute (source workers e.stage pub) f ((source workers e.stage pub).start e.state)
      m [] = some raw) (halt : raw.result = none) :
    bs = [[]] ∧ ls = [(e, raw)] ∧ final = after m (report (header pub) e raw).events := by
  cases h with
  | last call _ _ =>
    obtain ⟨rfl, rfl⟩ := execute_empty_forces_anyFuel run call
    exact ⟨rfl, rfl, rfl⟩
  | more call _ returned _ =>
    obtain ⟨_, rfl⟩ := execute_empty_forces_anyFuel run call
    rw [halt] at returned
    contradiction

/-- A closed empty-tape reference determines every tagged report of the stage.
Its linked writes and controller handoffs determine the exact physical image. -/
theorem Phase.canonical_empty {e phy bs ls final} (h : Phase workers pub cap e phy bs ls final)
    {f n : ℕ} {src : Memory w} {raws : List (Report w)}
    (run : runSegment (source workers e.stage pub) f (some e.state) src (List.replicate n []) =
      some raws) (halt : endState (some e.state) raws = none)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog raws)) :
    bs = List.replicate n [] ∧ ls = stageLogs e raws ∧
      final = after phy (eventLog (stageReports (header pub) e raws)) := by
  obtain ⟨choices, reports, _⟩ := h.force_empty src n f raws run halt agree reads
  exact ⟨choices, reports ▸ stageLogs_eq h, by rw [← h.final_memory, h.reports_eq, reports]⟩

open private agree_report from OAI.Computability.VPVNP.PairSimulationTerminalSplit

/-- Identify the bootstrap and prefix blocks of an actual five-stage accepting
trace using ordinary workers at their own fuel budgets. The bootstrap's
controller handoff supplies the memory agreement needed by the prefix. -/
theorem FiveTrace.canonical_start {m : Memory w} (t : FiveTrace workers pub cap m)
    {boot : Report w} {rows : List (Report w)} {f g n : ℕ}
    (bootRun : execute (source workers Stage.bootstrap pub) f
      ((source workers Stage.bootstrap pub).start 0) m [] = some boot) (closed : boot.result = none)
    (prefixRun : runSegment (source workers Stage.prefixRows pub) g (some 0) (after m boot.events)
      (List.replicate n []) = some rows) (halt : endState (some 0) rows = none)
    (reads : SourceTransport.Reads (workerCell (header pub)) (eventLog rows)) :
    let phy := after m (report (header pub) .initial boot).events
    let prefixEntry : Entry w := .resume Stage.prefixRows 0
    t.bootstrap.choices = [[]] ∧ t.bootstrap.logs = [(.initial, boot)] ∧
      t.bootstrap.memory = phy ∧ t.prefixRows.choices = List.replicate n [] ∧
      t.prefixRows.logs = stageLogs prefixEntry rows ∧
      t.prefixRows.memory = after phy (eventLog (stageReports (header pub) prefixEntry rows)) := by
  obtain ⟨bs, ls, mem⟩ := t.bootRun.force_oneShot bootRun closed
  have agree := agree_report (header pub) .initial boot m m (fun _ _ => rfl)
  rw [← mem] at agree
  obtain ⟨ps, logs, final⟩ := t.prefixRun.canonical_empty prefixRun halt agree reads
  exact ⟨bs, ls, mem, ps, logs, by simpa only [mem] using final⟩

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
