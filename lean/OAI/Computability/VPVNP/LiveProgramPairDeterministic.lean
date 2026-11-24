import OAI.Computability.VPVNP.LiveProgramTerminalStage

/-!
# Indexing a deterministic stage by its verified empty-choice execution

The invariant consists of the unconsumed part of the verified run. Exact
use of the input choices implies that every other accepted path begins
with the same calls and reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group
open BurstRAM BurstRAM.PrivateRAM LiveStageLink
open scoped Classical

variable {G : Group} {s : Stage} {m : Memory G.w} {calls : ℕ} {rs : List (Report G.w)}

private def HasTail (G : Group) (s : Stage) (st : Word G.w) (mem : Memory G.w) : Prop :=
  ∃ n logs, runSegment (sourceProgram G.T G.pub s) (G.clockAt s) (some st) mem (List.replicate n []) = some logs ∧
    endState (some st) logs = none ∧ PreservesTagOnReturns G.addr mem logs

private theorem tail_frame (G : Group) (s : Stage) : TagFrame G.T G.pub G.addr s (G.clockAt s) (HasTail G s) := by
  rintro st mem bits rep st' ⟨n,logs,run,halt,frame⟩ tag call cont
  cases n with
  | zero =>
    simp only [List.replicate_zero,runSegment,Option.some.injEq] at run
    subst logs; contradiction
  | succ n =>
    rw [List.replicate_succ,runSegment] at run
    cases h : execute (sourceProgram G.T G.pub s) (G.clockAt s) ((sourceProgram G.T G.pub s).start st) mem [] with
    | none => simp [h] at run
    | some r =>
      obtain ⟨rfl,rfl⟩ := execute_empty_forces h call
      simp only [h,Option.map_eq_some_iff] at run
      obtain ⟨rest,hrest,rfl⟩ := run
      refine ⟨⟨n,rest,?_,?_,frame.2⟩,(frame.1 (by simp [cont])).trans tag⟩
      · simpa only [cont] using hrest
      · change endState rep.result rest = none at halt
        simpa only [cont] using halt

/-- Index a deterministic stage by the unique unit value when its verified all-empty-choice
segment terminates, fits the linked clock, and preserves the tag on returns. -/
noncomputable def deterministicIndexed (tag : G.tagged s m)
    (run : runSegment (Pieces.component G.components s G.g G.lit) (G.clockAt s) (some 0) m
      (List.replicate calls []) = some rs)
    (halt : endState (some 0) rs = none)
    (fits : ∀ r ∈ rs, room G.nextStage G.addr s (G.clockAt s) r)
    (frame : PreservesTagOnReturns G.addr m rs) : Indexed G s m Unit := by
  have hsrc := (component_segment G s (G.clockAt s) (some 0) m (List.replicate calls [])).trans run
  let one : G.StagePaths s m := ⟨List.replicate calls [],rs,hsrc,halt,fits⟩
  refine ⟨⟨HasTail G s,tail_frame G s,⟨calls,rs,hsrc,halt,frame⟩,tag⟩,
    ⟨fun _ => one,fun _ => (),by intro u; cases u; rfl,?_⟩⟩
  intro p
  obtain ⟨logs,hr,hh,_⟩ := p.property
  obtain ⟨bs,tail,eq,_,runTail⟩ := split_empty_segment hsrc hr hh
  rw [halt] at runTail
  cases bs with
  | nil => exact Subtype.ext (by simpa only [List.append_nil] using eq.symm)
  | cons _ _ => contradiction

/-- Replaying the unique stage path returns the original, concrete reports. -/
theorem deterministic_reports (tag : G.tagged s m)
    (run : runSegment (Pieces.component G.components s G.g G.lit) (G.clockAt s) (some 0) m
      (List.replicate calls []) = some rs)
    (halt : endState (some 0) rs = none)
    (fits : ∀ r ∈ rs, room G.nextStage G.addr s (G.clockAt s) r)
    (frame : PreservesTagOnReturns G.addr m rs) :
    ordinaryReports ((deterministicIndexed tag run halt fits frame).traces ()) = rs := by
  apply Option.some.inj
  exact (ordinaryRun ((deterministicIndexed tag run halt fits frame).traces ())).symm.trans
    ((component_segment G s (G.clockAt s) (some 0) m _).trans run)

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
