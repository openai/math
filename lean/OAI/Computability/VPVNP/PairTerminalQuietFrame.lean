import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTerminalReachableFrame
import OAI.Computability.VPVNP.PairTraversalControllerMemory

/-!
# The low-memory frame of the linked bootstrap and width scan

Each canonical terminal burst is replayed on its own physical input memory.
The terminal controller writes the phase and the saved state above the packed
workspace. The width scan's own stores are confined to its live directory and
header words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM CompressorRecords Compression TerminalPrefix.Linked TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ}

/-- A source frame at one address survives the two linker stores, even when
the linked worker starts with different values at its control cells. -/
theorem replayFrame_stage (h : Word w) (e : Entry w) {x : ℕ} (away : workerCell h x)
    (rs : List (Report w)) (src phy : Memory w) (equal : src x = phy x)
    (frame : ReplayFrame x src rs) : ReplayFrame x phy (stageReports h e rs) := by
  induction rs generalizing src phy e with
  | nil => trivial
  | cons r rs ih =>
    have linked : after phy (report h e r).events x = after src r.events x := by
      rw [report_after]
      cases ht : target e.stage r.result with
      | none => exact ControllerMemory.after_at equal.symm _
      | some pair =>
        obtain ⟨s,v⟩ := pair
        simp only [writeMemory,ite_eq_right away.1,ite_eq_right away.2]
        exact ControllerMemory.after_at equal.symm _
    exact ⟨linked.trans (frame.1.trans equal), ih _ _ _ linked.symm frame.2⟩

private theorem appendReplay {x : ℕ} {m : Memory w} (as bs : List (Report w))
    (first : ReplayFrame x m as) (next : ReplayFrame x (after m (eventLog as)) bs) :
    ReplayFrame x m (as ++ bs) := by
  induction as generalizing m with
  | nil => exact next
  | cons r rs ih =>
    rw [show after m (eventLog (r :: rs)) = after (after m r.events) (eventLog rs) from
      List.foldl_append] at next
    exact ⟨first.1, ih first.2 next⟩

variable {a g : ℕ} {workers : Stage → LiveProgram.PairTable} {pub : Fin 11 → Word w}
variable {cap fuel : ℕ} {Y : State a g} {inc : IncidenceDirectory w} {starts : Word w}
variable {input : Memory w} {boot : Report w} {rs : List (Report w)}

/-- Recover the physical first two stages from any forced three-stage
prelude, including a prelude for which all later paths reject. -/
theorem QuietPrefix.force_start (q : QuietPrefix workers pub cap input)
    (s : Start workers pub cap fuel Y inc starts input boot rs)
    (clock₀ : fuel + 30 ≤ cap) (clock₁ : 60 ≤ cap) :
    q.boot.val.logs = [(.initial,boot)] ∧ q.boot.val.memory = bootMemory pub input boot ∧
    q.prefixRows.val.logs = stageLogs (.resume Stage.prefixRows 0) rs ∧
    q.prefixRows.val.memory = prefixMemory pub input boot rs := by
  obtain ⟨first,second⟩ := s.phases clock₀ clock₁
  obtain ⟨_,log₀,mem₀⟩ := first.force_quiet (by simp) q.boot.prop
  rw [← mem₀] at second
  obtain ⟨_,log₁,mem₁⟩ :=
    second.force_quiet (fun _ h => List.eq_of_mem_replicate h) q.prefixRows.prop
  exact ⟨log₀,mem₀,log₁,mem₁⟩

/-- Join the two canonical initialization phases to the frame for the actual
third-stage reports. All memories in the conclusion are the successive
physical memories of the selected three-stage trace. -/
theorem QuietPrefix.replayFrame_of_start (q : QuietPrefix workers pub cap input)
    (s : Start workers pub cap fuel Y inc starts input boot rs)
    (clock₀ : fuel + 30 ≤ cap) (clock₁ : 60 ≤ cap)
    (x : ℕ) (away : workerCell (header pub) x)
    (bootLow : after input boot.events x = input x)
    (prefixLow : ¬ TerminalPrefix.Segment.probeRegion pub inc starts
      (TerminalPrefix.arcCount Y) x)
    (third : ReplayFrame x q.prefixRows.val.memory
      (reports (header pub) q.traversalRows.val.logs)) :
    ReplayFrame x input q.reportList := by
  obtain ⟨logs₀,_,logs₁,_⟩ := q.force_start s clock₀ clock₁
  have raw : ∀ (m : Memory w) (ss : List (Report w)), (∀ r ∈ ss, r ∈ rs) → ReplayFrame x m ss := by
    intro m ss
    induction ss generalizing m with
    | nil => intro _; trivial
    | cons r ss ih =>
      intro contained
      have stores := (s.rawScan.accesses r (contained r (by simp))).2
      exact ⟨SourceTransport.after_outside _ stores prefixLow,
        ih _ (fun r hr => contained r (List.mem_cons_of_mem _ hr))⟩
  have frames₀ : ReplayFrame x input (reports (header pub) q.boot.val.logs) := by
    rw [logs₀]
    exact replayFrame_stage (header pub) .initial away [boot] input input rfl ⟨bootLow,trivial⟩
  have frames₁ : ReplayFrame x q.boot.val.memory (reports (header pub) q.prefixRows.val.logs) := by
    rw [logs₁,reports_stageLogs]
    apply replayFrame_stage (header pub) _ away _ q.boot.val.memory q.boot.val.memory rfl
    exact raw _ _ (fun _ h => h)
  change ReplayFrame x input (reports (header pub)
    (q.boot.val.logs ++ (q.prefixRows.val.logs ++ q.traversalRows.val.logs)))
  simp only [reports,List.map_append]
  apply appendReplay _ _ frames₀
  rw [q.boot.prop.final_memory]
  apply appendReplay _ _ frames₁
  rw [q.prefixRows.prop.final_memory]
  exact third

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
