import OAI.Computability.VPVNP.LiveProgramTerminalStage

/-!
# Handoff of a deterministic evaluator stage in the complete live program

A successful standalone scan has one empty choice string per call. If its
returning reports preserve the stage tag, the outer dispatcher adds its
exact reports, retags the final memory and starts the next stage at zero.
The inverse direction removes this forced prefix from every accepted path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM LiveStageLink

variable (G : Group)

/-- Add the group dispatch and handoff events to each source report of the selected stage. -/
abbrev linkedLogs (s : Stage) (rs : List (Report G.w)) := rs.map (linkedReport G.nextStage G.addr s)

theorem component_completion {s : Stage} {fuel : ℕ} {st : Word G.w} {m : Memory G.w}
    {bs : List (List Bool)} {rs : List (Report G.w)} (fit : fuel + 47 ≤ G.clock)
    (ht : G.tagged s m) (frame : PreservesTagOnReturns G.addr m rs)
    (run : runSegment (Pieces.component G.components s G.g G.lit) fuel (some st) m bs = some rs)
    (halt : endState (some st) rs = none) :
    runSegment G.P G.clock (some st) m bs = some (G.linkedLogs s rs) ∧
    endState (some st) (G.linkedLogs s rs) = (G.nextStage s).map (fun _ => 0) ∧
    after m (eventLog (G.linkedLogs s rs)) = transferMemory G.addr (G.nextStage s) (after m (eventLog rs)) ∧
    RAMBuckets.cost Report.probes (G.linkedLogs s rs) =
      RAMBuckets.cost Report.probes rs + rs.length + (if (G.nextStage s).isSome then 1 else 0) :=
  runSegment_accepting G.T G.nextStage G.pub G.addr s G.tagFit fit st m bs rs ht frame
    ((component_segment G s ..).trans run) halt

/-- Each accepted continuation corresponds to exactly one complete choice
stream with the verified empty-choice prefix. The cap includes every
dispatch, return and final stage transfer in that prefix. -/
noncomputable def deterministicHandoff {s dest : Stage} {fuel n : ℕ} {m m' : Memory G.w}
    {rs : List (Report G.w)} (fit : fuel + 47 ≤ G.clock) (ht : G.tagged s m)
    (frame : PreservesTagOnReturns G.addr m rs) (hn : G.nextStage s = some dest)
    (run : runSegment (Pieces.component G.components s G.g G.lit) fuel (some 0) m
      (List.replicate n []) = some rs)
    (halt : endState (some (0 : Word G.w)) rs = none) (hm : after m (eventLog rs) = m')
    (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (writeMemory m' G.addr (tagWord G.w dest))
      (fun tail => cap (G.linkedLogs s rs ++ tail)) ≃ ActualPaths G.P G.clock 0 m cap := by
  obtain ⟨h, hstate, hmem, _⟩ := G.component_completion fit ht frame run halt
  have e := emptySegmentEquiv h cap
  rw [hstate, hmem, hn, hm] at e
  exact e

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
