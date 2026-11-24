import OAI.Computability.VPVNP.RAMProcessorScanBounds
import OAI.Computability.VPVNP.RAMProcessorCallInvariant

/-!
# Returning a private event prefix from a physical call segment

The internal instruction scan contributes ticks and private branch choices to
the report. Its prefix consumes no external probes, so it leaves the costs,
record timestamps, and emitted slots of the external continuation intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ}

theorem countProbes_append (xs ys : List (Event w)) :
    countProbes (xs++ys) = countProbes xs + countProbes ys := by
  induction xs with
  | nil => simp [countProbes]
  | cons x xs ih => cases x <;> simp [countProbes, ih, Nat.add_assoc]

theorem eventRecords_append (start ord : ℕ) (xs ys : List (Event w)) :
    eventRecords start ord (xs++ys) = eventRecords start ord xs ++
      eventRecords start (ord+countProbes xs) ys := by
  induction xs generalizing ord with
  | nil => simp [eventRecords, countProbes]
  | cons x xs ih => cases x <;> simp [eventRecords, countProbes, ih, Nat.add_assoc]

/-- Prepend an ordered event prefix to a call report and retain its final result. -/
def Report.withEvents (prefixEvents : List (Event w)) (r : Report w) : Report w :=
  ⟨prefixEvents++r.events, r.result⟩

end BurstRAM

namespace RAMTape.LocalProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

theorem addEvents_eq (xs : List (Event w)) (out : Output w) :
    addEvents xs out = out.map (fun z => (z.1.withEvents xs, z.2)) := by
  induction xs with
  | nil => cases out <;> simp [addEvents, Report.withEvents]
  | cons e xs ih =>
    cases out with
    | none => simp [addEvents, ih, addEvent]
    | some z => rcases z with ⟨r,bs⟩; simp [addEvents, ih, addEvent, Report.withEvents, Report.prepend]

theorem scan_probeCount (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) :
    countProbes (scan T pub f c bs).prefixEvents = 0 := by
  rw [← length_eventRecords 0 0, scan_no_probes]
  rfl

end RAMTape.LocalProcessor

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- Number of further probes admitted by all three budgets, the minimum of the remaining call,
global and site credits. -/
def allowance (s : Snapshot w p r k) := min s.callLeft (min s.globalLeft.val s.siteLeft)

theorem InCall.afterLocal (T : Template p r k) {s : Snapshot w p r k} {ys start ord}
    (hin : InCall hw H F s ys start ord) :
    InCall hw H F (s.afterLocal (LocalProcessor.scan T s.pub s.fuel s.cfg s.choices)) ys start ord := by
  let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
  have hpc := (LocalProcessor.scan_writes_le T s.pub s.fuel s.cfg s.choices).trans hin.privateClock
  refine ⟨?_, hin.savedEq, hin.ordinalEq, hin.timestamp⟩
  exact {hin.toCallReady with privateClock := hpc, buffer := {
    fit := hin.buffer.fit, scratch := rfl, zeros := rfl, remaining := hin.buffer.remaining,
    buffer := hin.buffer.buffer, output := hin.buffer.output }}

theorem CallReturn.privatePrefix (T : Template p r k) {s u : Snapshot w p r k} {ys zs start ord r tail}
    (h : CallReturn (s.afterLocal (LocalProcessor.scan T s.pub s.fuel s.cfg s.choices)) u ys zs start ord r tail) :
    CallReturn s u ys zs start ord (r.withEvents (LocalProcessor.scan T s.pub s.fuel s.cfg s.choices).prefixEvents) tail := by
  have hz := LocalProcessor.scan_probeCount T s.pub s.fuel s.cfg s.choices
  have hn := LocalProcessor.scan_no_probes T s.pub s.fuel s.cfg s.choices start.val ord.val
  refine ⟨h.pub, h.H, h.fuel, h.cap, h.boundary, ?_, ?_, h.state, ?_, h.bits, ?_⟩
  · exact h.target
  · simpa [Snapshot.afterLocal, Report.probes, Report.withEvents, countProbes_append, hz] using h.cost
  · simpa [Snapshot.afterLocal, Report.probes, Report.withEvents, countProbes_append, hz] using h.siteLeft
  · simpa [Report.withEvents, eventRecords_append, hn, hz] using h.records

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
