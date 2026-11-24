import OAI.Computability.VPVNP.CompressorWorkspaceIntervals
import OAI.Computability.VPVNP.RAMFinite

/-! # Source reports of actual framed descriptor intervals

The six pointer reads are charged once per source call. The core clock can
be smaller than the clock of the framed table. Along concatenation the second
interval sees exactly the memory and cursor returned by the first. This
retains the actual core runs for charging work across repeated block visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineWorkspace
open BurstRAM BlockPlanner Schedule BranchSegments

variable {w clock cap : ℕ} {A : Script} {pub : Fin 11 → Word w}
local notation "pt" => ports (C := A.catalog) pub
local notation "inner" => Online.program A.plan pt
local notation "outer" => program A.plan pub

theorem framed_append (base : Word w) (m : Memory w) (rs ts : List (Report w)) :
    framed base m (rs++ts) = framed base m rs ++ framed base (after m (eventLog rs)) ts := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append,framed,ih,eventLog,List.flatMap_cons,after,List.foldl_append]

/-- A selected physical interval retains the inner machine's true reports
and native execution on its own private clock. -/
structure Core (A : Script) (pub : Fin 11 → Word w) {st : Option (Word w)} {m : Memory w} (s : Segment (program A.plan pub) clock st m) (cap : ℕ) where
  /-- Reports produced by the inner online program on the segment's branch tapes and private
  clock. -/
  logs : List (Report w)
  run : runSegment (Online.program A.plan (ports (C := A.catalog) pub)) cap st m s.bits = some logs
  frame : s.logs = framed (pub 2) m logs

namespace Core

variable {st : Option (Word w)} {m : Memory w} {s : Segment (program A.plan pub) clock st m} (source : Core A pub s cap)

theorem state : endState st source.logs = s.state := by
  rw [Segment.state,source.frame,(framed_effect (pub 2) m source.logs st).1]

theorem memory : after m (eventLog source.logs) = s.memory := by
  rw [Segment.memory,source.frame,(framed_effect (pub 2) m source.logs st).2.1]

/-- Join consecutive core runs by passing the first segment's returned state and memory to the
second. -/
def append {t : Segment outer clock s.state s.memory} (next : Core A pub t cap) : Core A pub (s.append t) cap where
  logs := source.logs ++ next.logs
  run := by
    change runSegment _ _ _ _ (s.bits++t.bits) = _
    rw [PrimedSchedule.runSegment_append,source.run,Option.bind_some,source.state,source.memory,next.run]
    rfl
  frame := by
    change s.logs++t.logs = _
    rw [framed_append,source.memory,← next.frame,← source.frame]

@[simp] theorem cost_append {t : Segment outer clock s.state s.memory} (next : Core A pub t cap) :
    RAMBuckets.cost Report.probes (source.append next).logs =
      RAMBuckets.cost Report.probes source.logs + RAMBuckets.cost Report.probes next.logs :=
  RAMBuckets.cost_append ..

/-- The chosen core clock bounds every actual source report, even when the
enclosing table gives the worker a larger clock. -/
theorem ticks (r : Report w) (hr : r ∈ source.logs) : r.events.length < cap :=
  localSegment_event_bound ((runSegment_iff ..).mp source.run).1 r hr

end Core

/-- Recover the inner reports and execution of a segment framed using the installed pointer
bank. -/
def framedSegmentCore {st : Option (Word w)} {m : Memory w}
    (s : Segment inner cap st m) (bank : Banks (arity A.catalog) (pub 2) m s.logs) :
    Core A pub (framedSegment A.plan pub s bank) cap := ⟨s.logs,s.run,rfl⟩

variable {m : Memory w}

/-- The exact core reports of the closing physical call. -/
def terminalCore {small : ℕ} (bounds : Online.Run.ControlBounds A.plan cap (w := w))
    (smallBounds : Online.Run.ControlBounds A.plan small (w := w))
    (htag : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex A.size A.size))
    (bank : Workspace.Installed (arity A.catalog) (pub 2) m) (stop : m (pt).rows.val ≤ m (pt).ordinal.val) :
    Core A pub (terminalSegment A pub bounds htag bank stop) small where
  logs := [Online.linked pt (Online.calendarIndex A.size A.size) (LevelCalendar.closedReport (pt).data m)]
  run := by
    change runSegment inner small (some 0) m [[]] = _
    rw [runSegment,Online.calendar_stop A.plan pt 0 m htag smallBounds.tags stop (by have := smallBounds.calendar; omega)]
    rfl
  frame := rfl

theorem terminal_cost {small : ℕ} (bounds : Online.Run.ControlBounds A.plan cap (w := w))
    (smallBounds : Online.Run.ControlBounds A.plan small (w := w))
    (htag : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex A.size A.size))
    (bank : Workspace.Installed (arity A.catalog) (pub 2) m) (stop : m (pt).rows.val ≤ m (pt).ordinal.val) :
    RAMBuckets.cost Report.probes (terminalCore (A := A) (pub := pub) bounds smallBounds htag bank stop).logs = 4 := by
  have hp := (Online.terminal_effect (d := A.size) (initial := A.initial.length) (phases := A.block.length) pt m).2.2.1
  change 1+_+0=4
  rw [hp]

end CompressorRecords.OnlineWorkspace

end VPVNP
end Computability
end OAI
