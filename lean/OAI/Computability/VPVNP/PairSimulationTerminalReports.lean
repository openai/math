import OAI.Computability.VPVNP.PairSimulationTerminalEnter
import OAI.Computability.VPVNP.PairSimulationTerminalBody
import OAI.Computability.VPVNP.LiveStageLinkPaths

/-!
# Observable terminal calls and their resource charges

A terminal worker is entered either at bootstrap or with a restored state.
The report keeps each source choice in order, charges at most four additional
probes and thirty additional events, and determines both header cells used by
the next call. The final successful exit leaves the source memory result.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM
open scoped Fin.CommRing
open private probe_append bits_append ticks after_ticks from OAI.Computability.VPVNP.LiveStageLinkPaths

variable {w : ℕ}

/-- A fresh terminal invocation or a resumed stage with its saved state. -/
inductive Entry (w : ℕ)
  | initial
  | resume (stage : Stage) (state : Word w)
  deriving DecidableEq

/-- Worker selected by this entry. -/
def Entry.stage : Entry w → Stage
  | .initial => 0
  | .resume s _ => s

/-- Persistent word passed to the selected worker. -/
def Entry.state : Entry w → Word w
  | .initial => 0
  | .resume _ x => x

/-- Persistent word received by the enclosing terminal program. -/
def Entry.marker : Entry w → Word w
  | .initial => 0
  | .resume .. => 1

/-- Physical events that enter the selected worker. -/
def Entry.prefixEvents (addr : Word w) : Entry w → List (Event w)
  | .initial => initialEvents w
  | .resume s x => dispatchEvents addr x s

/-- The external stage and state cells encode a resumed entry. -/
def Entry.Valid (addr : Word w) (m : Memory w) : Entry w → Prop
  | .initial => True
  | .resume s x => m addr.val = tagWord w s ∧ m (addr+31).val = x

/-- Number of external reads used to enter this worker. -/
def Entry.reads : Entry w → ℕ
  | .initial => 0
  | .resume .. => 2

/-- Next terminal entry after the worker's report. -/
def Entry.follow (e : Entry w) (rep : Report w) : Option (Entry w) :=
  (target e.stage rep.result).map fun (s,v) => .resume s v

/-- Complete physical report, including entry and exit events. -/
def report (addr : Word w) (e : Entry w) (rep : Report w) :=
  LiveStageLink.prependLog (e.prefixEvents addr) (exitReport addr e.stage rep)

theorem prefix_length_le (addr : Word w) (e : Entry w) : (e.prefixEvents addr).length ≤ 26 := by
  cases e with
  | initial => simp [Entry.prefixEvents]
  | resume s x => simp [Entry.prefixEvents]; have := s.isLt; omega

private theorem prefix_bits (addr : Word w) (e : Entry w) : choiceBits (e.prefixEvents addr) = [] := by
  cases e <;> simp [Entry.prefixEvents,initialEvents,dispatchEvents,choiceBits,(ticks (w := w) _).2]

private theorem prefix_probes (addr : Word w) (e : Entry w) : countProbes (e.prefixEvents addr) = e.reads := by
  cases e <;> simp [Entry.prefixEvents,Entry.reads,initialEvents,dispatchEvents,countProbes,(ticks (w := w) _).1]

private theorem after_append (m : Memory w) (a b : List (Event w)) : after m (a++b) = after (after m a) b :=
  List.foldl_append

private theorem after_prefix (addr : Word w) (e : Entry w) (m : Memory w) : after m (e.prefixEvents addr) = m := by
  cases e with
  | initial => exact after_ticks 13 m
  | resume s x =>
    rw [Entry.prefixEvents,dispatchEvents,after_append,after_append,after_ticks]
    change after m (List.replicate _ .tick) = _
    exact after_ticks _ m

theorem report_bits (addr : Word w) (e : Entry w) (rep : Report w) :
    choiceBits (report addr e rep).events = choiceBits rep.events := by
  simp only [report,LiveStageLink.prependLog,bits_append,prefix_bits,List.nil_append]
  unfold exitReport
  cases h : target e.stage rep.result with
  | none => rfl
  | some p => cases p; simp [exitEvents,bits_append,choiceBits]

theorem report_probes (addr : Word w) (e : Entry w) (rep : Report w) :
    (report addr e rep).probes = rep.probes+e.reads+(if (e.follow rep).isSome then 2 else 0) := by
  simp only [report,Report.probes,LiveStageLink.prependLog,probe_append,prefix_probes]
  unfold exitReport Entry.follow
  cases h : target e.stage rep.result with
  | none => simp [Nat.add_comm]
  | some p => cases p; simp [exitEvents,probe_append,countProbes]; omega

theorem report_probes_le (addr : Word w) (e : Entry w) (rep : Report w) :
    (report addr e rep).probes ≤ rep.probes+4 := by
  rw [report_probes]
  cases e <;> simp only [Entry.reads] <;> split <;> omega

theorem report_length_le (addr : Word w) (e : Entry w) (rep : Report w) :
    (report addr e rep).events.length ≤ rep.events.length+30 := by
  have h := prefix_length_le addr e
  simp only [report,LiveStageLink.prependLog,List.length_append]
  unfold exitReport
  cases v : target e.stage rep.result with
  | none => change (e.prefixEvents addr).length + rep.events.length ≤ _; omega
  | some p => cases p; simp [exitEvents]; omega

theorem report_result (addr : Word w) (e : Entry w) (rep : Report w) :
    (report addr e rep).result = (e.follow rep).map Entry.marker := by
  cases hr : rep.result <;> cases hn : next e.stage <;>
    simp [report,LiveStageLink.prependLog,exitReport,Entry.follow,target,Entry.marker,hr,hn]

theorem report_after (addr : Word w) (e : Entry w) (rep : Report w) (m : Memory w) :
    after m (report addr e rep).events =
      match target e.stage rep.result with
      | none => after m rep.events
      | some (s,v) => writeMemory (writeMemory (after m rep.events) addr (tagWord w s)) (addr+31) v := by
  rw [report,LiveStageLink.prependLog,after_append,after_prefix]
  unfold exitReport
  cases ht : target e.stage rep.result with
  | none => rfl
  | some p => cases p; rw [after_append]; rfl

theorem next_valid (addr : Word w) (e e' : Entry w) (rep : Report w) (m : Memory w)
    (fit : 32 ≤ 2^w) (step : e.follow rep = some e') :
    e'.Valid addr (after m (report addr e rep).events) := by
  have ne : addr.val ≠ (addr+31).val := by
    intro eq
    have he : addr+31 = addr+0 := (Fin.ext eq.symm).trans (add_zero _).symm
    have hz := congrArg Fin.val (add_left_cancel he : (31 : Word w) = 0)
    change 31 % 2^w = 0 at hz
    rw [Nat.mod_eq_of_lt (by omega)] at hz
    contradiction
  unfold Entry.follow at step
  cases h : target e.stage rep.result with
  | none => simp [h] at step
  | some p =>
    obtain ⟨s,v⟩ := p
    have he : e' = .resume s v := by simpa [h] using step.symm
    subst e'
    simp [Entry.Valid,report_after,h,writeMemory,ne]

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
