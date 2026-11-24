import OAI.Computability.VPVNP.CompressorSourceSequence
import OAI.Computability.VPVNP.CompressorWorkspaceBranchCut
import OAI.Computability.VPVNP.LiveStagePaths

/-! # Framed descriptor intervals and the terminal calendar call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM Schedule BranchSegments BlockPlanner DescriptorSpace
open scoped Fin.CommRing

variable {w cap : ℕ}

theorem SourceBankFrame.Stable.framed {lo : ℕ} {m : Memory w} {rs : List (Report w)}
    (base : Word w) (h : SourceBankFrame.Stable lo m rs) :
    SourceBankFrame.Stable lo m (OnlineWorkspace.framed base m rs) := by
  induction rs generalizing m with
  | nil => trivial
  | cons r rs ih =>
    rw [OnlineWorkspace.framed,SourceBankFrame.Stable,(Workspace.report_effect base m r).2.2.2.1]
    exact ⟨h.1,ih h.2⟩

private theorem returning_reports {Q : Type*} {P : BurstRAM.Program w Q} {st : Option (Word w)}
    {m : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (run : runSegment P cap st m bs = some rs) (cont : endState st rs ≠ none) :
    ∀ r ∈ rs, r.result ≠ none ∧ r.events.length < cap := by
  induction bs generalizing st m rs with
  | nil => change some [] = some rs at run; obtain rfl := Option.some.inj run; simp
  | cons b bs ih =>
    cases st with
    | none => contradiction
    | some st =>
      cases hr : execute P cap (P.start st) m b with
      | none => simp [runSegment,hr] at run
      | some r =>
        simp only [runSegment,hr,Option.map_eq_some_iff] at run
        obtain ⟨tail,rest,rfl⟩ := run
        rw [List.forall_mem_cons]
        refine ⟨⟨?_,(execute_spec hr).1.length_lt⟩,ih rest cont⟩
        intro halted
        rw [halted] at rest
        cases bs with
        | nil => change some [] = some tail at rest; obtain rfl := Option.some.inj rest; exact cont halted
        | cons => contradiction

/-- Every report of a returning segment fits the enclosing link: the link
adds transfer instructions only to the component's accepting report. -/
theorem BranchSegments.Segment.link_room {Q : Type*} {P : BurstRAM.Program w Q} {st : Option (Word w)}
    {m : Memory w} (s : Segment P cap st m) (cont : s.state ≠ none)
    {d : ℕ} (next : Fin d → Option (Fin d)) (addr : Word w) (stage : Fin d) :
    ∀ r ∈ s.logs, LiveStageLink.room next addr stage cap r := by
  intro r hr
  have ⟨ret,hlen⟩ := returning_reports s.run cont r hr
  cases eqn : r.result with
  | none => exact (ret eqn).elim
  | some st => simpa only [LiveStageLink.room,LiveStageLink.exitReport,eqn] using hlen

namespace OnlineWorkspace

variable (A : Script) (pub : Fin 11 → Word w)
local notation "pt" => Workspace.ports (arity A.catalog) (pub 2)
local notation "prog" => program A.plan pub
variable {m : Memory w} (bounds : Online.Run.ControlBounds A.plan cap (w := w))
variable (htag : m (Workspace.ports (arity A.catalog) (pub 2)).tag.val =
    LiveStageLink.tagWord w (Online.calendarIndex A.size A.size)) (steps : List (Online.Run.Step A.size A.size w))
variable (valid : Online.Run.Interval A.plan (Workspace.ports (arity A.catalog) (pub 2)) cap m steps)
variable (stable : SourceBankFrame.Stable ((pub 2).val+6) m (Online.Run.intervalLog A.plan (Workspace.ports (arity A.catalog) (pub 2)) m steps))
variable (bank : Workspace.Installed (arity A.catalog) (pub 2) m)

/-- Run the chronological interval obtained from the actual source packets by
`SourceOnline.interval_stable`, reading the six stable pointers on every call. -/
def intervalSegment : Segment prog (cap+24) (some 0) m :=
  framedSegment A.plan pub (Online.Run.intervalSegment A.plan pt bounds htag steps valid) (stable.banks bank)

@[simp] theorem intervalSegment_state :
    (intervalSegment A pub bounds htag steps valid stable bank).state = some 0 := by
  exact (framedSegment_state A.plan pub (Online.Run.intervalSegment A.plan pt bounds htag steps valid)
    (stable.banks bank)).trans (Online.Run.interval_state_zero A.plan pt bounds htag steps valid)

@[simp] theorem intervalSegment_memory :
    (intervalSegment A pub bounds htag steps valid stable bank).memory = Online.Run.finalMemory (C := A.catalog) pt m steps := by
  exact (framedSegment_memory A.plan pub (Online.Run.intervalSegment A.plan pt bounds htag steps valid)
    (stable.banks bank)).trans (Online.Run.interval_memory A.plan pt bounds htag steps valid)

theorem intervalSegment_stable :
    SourceBankFrame.Stable ((pub 2).val+6) m (intervalSegment A pub bounds htag steps valid stable bank).logs :=
  stable.framed _

theorem intervalSegment_bank :
    Workspace.Installed (arity A.catalog) (pub 2) (intervalSegment A pub bounds htag steps valid stable bank).memory := by
  let s := intervalSegment A pub bounds htag steps valid stable bank
  have h := (intervalSegment_stable A pub bounds htag steps valid stable bank).installed bank s.logs.length
  rw [List.take_length] at h
  exact h

theorem intervalSegment_quiet (quiet : ∀ s ∈ steps, s.row.choices = List.replicate s.row.choices.length []) :
    let segment := intervalSegment A pub bounds htag steps valid stable bank
    segment.bits = List.replicate segment.bits.length [] := Online.Run.quietInterval steps quiet

/-- The one final framed calendar call executes its empty tape and halts. -/
def terminalSegment (stop : m (pt).rows.val ≤ m (pt).ordinal.val) : Segment prog (cap+24) (some 0) m where
  bits := [[]]
  logs := [Workspace.report (pub 2) m (Online.linked pt (Online.calendarIndex A.size A.size)
    (LevelCalendar.closedReport (pt).data m))]
  run := by
    have hc := Online.calendar_stop A.plan pt 0 m htag bounds.tags stop (by have := bounds.calendar; omega : _ ≤ cap)
    rw [runSegment,execute_dispatch A.plan pub 0 m [] _ bank,Nat.add_sub_cancel,hc]
    rfl

@[simp] theorem terminalSegment_state (stop : m (pt).rows.val ≤ m (pt).ordinal.val) :
    (terminalSegment A pub bounds htag bank stop).state = none :=
  (Online.terminal_effect (d := A.size) (initial := A.initial.length) (phases := A.block.length) pt m).1

@[simp] theorem terminalSegment_memory (stop : m (pt).rows.val ≤ m (pt).ordinal.val) :
    (terminalSegment A pub bounds htag bank stop).memory = m := by
  simp only [Segment.memory,terminalSegment,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [(Workspace.report_effect _ _ _).2.2.2.1]
  exact (Online.terminal_effect (d := A.size) (initial := A.initial.length) (phases := A.block.length) pt m).2.1

theorem terminalSegment_stable (stop : m (pt).rows.val ≤ m (pt).ordinal.val) (lo : ℕ) :
    SourceBankFrame.Stable lo m (terminalSegment A pub bounds htag bank stop).logs := by
  let r := Online.linked pt (Online.calendarIndex A.size A.size) (LevelCalendar.closedReport (pt).data m)
  change (∀ x < lo, after m (Workspace.report (pub 2) m r).events x = m x) ∧ True
  rw [(Workspace.report_effect _ _ _).2.2.2.1]
  have hm := (Online.terminal_effect (d := A.size) (initial := A.initial.length) (phases := A.block.length) pt m).2.1
  exact ⟨fun x _ => congrFun hm x,trivial⟩

/-- The terminal calendar call fits with all three outer transfer instructions. -/
theorem terminalSegment_room (stop : m (pt).rows.val ≤ m (pt).ordinal.val)
    {d : ℕ} (next : Fin d → Option (Fin d)) (addr : Word w) (stage : Fin d) :
    ∀ r ∈ (terminalSegment A pub bounds htag bank stop).logs, LiveStageLink.room next addr stage (cap+24) r := by
  let src := Online.linked pt (Online.calendarIndex A.size A.size) (LevelCalendar.closedReport (pt).data m)
  let r := Workspace.report (pub 2) m src
  intro rep hr
  obtain rfl : rep = r := List.mem_singleton.mp hr
  have small := Online.calendar_stop A.plan pt 0 m htag bounds.tags stop (cap := cap-3)
    (by have := bounds.calendar; omega)
  have length : src.events.length < cap-3 := (execute_spec small).1.length_lt
  have framedLen : r.events.length = 24+src.events.length := (Workspace.report_effect _ _ _).1
  have halted : r.result = none :=
    (Workspace.report_effect _ _ _).2.2.2.2.trans
      (Online.terminal_effect (d := A.size) (initial := A.initial.length) (phases := A.block.length) pt m).1
  cases ht : next stage <;>
    simp only [LiveStageLink.room,LiveStageLink.exitReport,halted,ht,LiveStageLink.transferEvents,List.length_append,
      List.length_cons,List.length_nil,framedLen] <;> omega

end OnlineWorkspace
end CompressorRecords

end VPVNP
end Computability
end OAI
