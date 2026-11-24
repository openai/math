import OAI.Computability.VPVNP.PairSimulationTerminalPartialFrames
import OAI.Computability.VPVNP.PairSimulationTerminalDeterministic
import OAI.Computability.VPVNP.LiveTerminalReachableFrame

/-!
# Protecting a live word on every reached call of the terminal program

The forced startup, prefix and traversal blocks reach the physical bit-scan
memory. The remaining two worker controls apply to every successful call,
including histories which a later site rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ} {m : Memory w}

/-- All branch tapes supplied to the three deterministic setup phases, in call order. -/
def QuietPrefix.choices (q : QuietPrefix workers pub cap m) :=
  q.boot.val.choices ++ (q.prefixRows.val.choices ++ q.traversalRows.val.choices)

/-- The original worker reports paired with their terminal-controller entries. -/
def QuietPrefix.logs (q : QuietPrefix workers pub cap m) :=
  q.boot.val.logs ++ (q.prefixRows.val.logs ++ q.traversalRows.val.logs)

/-- The physical reports after the controller has wrapped every setup call. -/
def QuietPrefix.reportList (q : QuietPrefix workers pub cap m) := reports (header pub) q.logs

private theorem QuietPrefix.empty_choices (q : QuietPrefix workers pub cap m) :
    q.choices = List.replicate q.choices.length [] := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_replicate]
    have mem := List.getElem_mem (l := q.choices) hj
    change _ ∈ q.boot.val.choices ++ (q.prefixRows.val.choices ++ q.traversalRows.val.choices) at mem
    rcases List.mem_append.mp mem with hb | rest
    · exact q.bootQuiet _ hb
    rcases List.mem_append.mp rest with hp | hr
    · exact q.prefixQuiet _ hp
    · exact q.traversalQuiet _ hr

theorem QuietPrefix.replay (q : QuietPrefix workers pub cap m) (fit : 32 ≤ 2^w) (enough : 26 ≤ cap) :
    runSegment (program workers pub) cap (some 0) m (List.replicate q.choices.length []) = some q.reportList := by
  have visits : Visits workers pub cap (some .initial) m q.choices q.logs := by
    apply q.boot.prop.append_visits
    apply q.prefixRows.prop.append_visits
    change Visits workers pub cap (some (.resume Stage.traversalRows 0)) _ _ _
    simpa only [List.append_nil] using q.traversalRows.prop.append_visits (.nil _ _)
  rw [← q.empty_choices]
  exact visits.native workers pub cap fit enough (by rintro e h; cases h; trivial)

theorem QuietPrefix.endSetup (q : QuietPrefix workers pub cap m) :
    endState (some 0) q.reportList = some (Entry.resume Stage.sharedBits (0 : Word w)).marker := by
  change endState (hostState (some .initial)) (reports (header pub) q.logs) = _
  rw [finish_host,QuietPrefix.logs,q.boot.prop.finish_append]
  change hostState (finish (some (.resume Stage.prefixRows 0)) _) = _
  rw [q.prefixRows.prop.finish_append]
  change hostState (finish (some (.resume Stage.traversalRows 0)) q.traversalRows.val.logs) = _
  have last := q.traversalRows.prop.finish_append []
  rw [List.append_nil] at last
  rw [last]
  rfl

theorem QuietPrefix.after_setup (q : QuietPrefix workers pub cap m) :
    after m (eventLog q.reportList) = q.traversalRows.val.memory := by
  have append (start : Memory w) (xs ys : List (Log w)) :
      after start (eventLog (reports (header pub) (xs++ys))) =
        after (after start (eventLog (reports (header pub) xs))) (eventLog (reports (header pub) ys)) := by
    simp only [reports,List.map_append,eventLog,List.flatMap_append,after,List.foldl_append]
  rw [QuietPrefix.reportList,QuietPrefix.logs,append,q.boot.prop.final_memory,append,
    q.prefixRows.prop.final_memory,q.traversalRows.prop.final_memory]

/-- The protected-address property includes both continuing calls and the
last accepting exit. The setup frame is measured on its actual memory at
each report. The vertex invariant may depend on the fourth block. -/
theorem QuietPrefix.preservesCell (q : QuietPrefix workers pub cap m) (a : ℕ)
    (fit : 32 ≤ 2^w) (enough : 26 ≤ cap)
    (prefixFrame : ReplayFrame a m q.reportList)
    (valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) q.traversalRows.val.memory)
    (bit : WorkerControl workers pub cap Stage.sharedBits a q.traversalRows.val.memory)
    (vertex : ∀ b : q.BitPaths, WorkerControl workers pub cap Stage.vertices a b.val.memory) :
    PreservesCell (program workers pub) cap 0 m a := by
  apply preservesCell_after_replayed_prefix (q.replay fit enough) q.endSetup prefixFrame
  rw [q.after_setup]
  exact shared_vertices_safe bit vertex fit enough valid

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
