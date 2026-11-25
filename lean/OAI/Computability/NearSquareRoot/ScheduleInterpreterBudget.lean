import OAI.Computability.NearSquareRoot.ScheduleInterpreterTimed
import OAI.Computability.NearSquareRoot.ScheduleInterpreterClockPulse

/-!
# A fenced interpreter trial including its physical budget clock

Two additional physical tape heads maintain the binary clock. At an allotted
tick they execute one transition of the interpreter protected by the common
fences. The terminal code distinguishes ordinary output, rejection and timeout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Budget

open IntegerMultiplication TM

variable {A Q I : Type}

abbrev controller (blank : A) [Fintype I] (m : Rule A Q I) :=
  Timed.rule (blank, false, false) none (Fence.guard m)
    ScheduleClock.PhysicalRule ScheduleClock.physicalPulse

/-- Starting with a unary budget exponent and canonical marked work tapes, the
combined machine reaches a terminal configuration. Decoding it agrees exactly
with the scheduler's bounded trial for this exponent. -/
theorem run [Fintype I] (m : Rule A Q I) (blank : A) (lo hi : I → ℤ) (x : Config A Q I)
    (hx : Fence.within lo hi x) (e : List Bool) (T : Bool → Tape (Option Bool))
    (hf : SM.faithful (ScheduleClock.cfg .initialize [] e).stack T) :
    let start := Timed.pack (Fence.marked lo hi false x) (⟨.inl .initialize,T⟩ :
      ScheduleClock.ClockConfiguration)
    ∃ t ≤ 2*(e.length+1+6*2^e.length), ∃ y c,
      Trace (advance (controller blank m)) start t (Timed.pack y c) ∧
      advance (controller blank m) (Timed.pack y c) = none ∧
      Timed.answer ScheduleClock.PhysicalRule (fun q => !q.1) y c =
        Schedule.tryFor (tapeTick (Fence.guard m) (fun q => !q.1)) (2^e.length)
          (Fence.marked lo hi false x) ∧
      VisitsAtMost (controller blank m) start t
        ((∑ i : I, (hi i+1-lo i).toNat) + 2*(e.length+3)) := by
  obtain ⟨k,T',clk,halt,kBound,cSpace⟩ := ScheduleClock.physical_expiration_pulses e T hf
  obtain ⟨t, ht, y, c, hist, done, out⟩ := Timed.execute (blank,false,false) none (Fence.guard m)
    ScheduleClock.PhysicalRule ScheduleClock.physicalPulse (fun q => !q.1)
    (Fence.marked lo hi false x) clk halt
  refine ⟨t,ht.trans kBound,y,c,hist,done,by simpa using out,?_⟩
  apply Timed.visits
  · exact Fence.trial_visited m lo hi x hx t
  · obtain ⟨cells, hc, ps⟩ := cSpace
    exact ⟨cells, hc, fun u hu st hu' i => ps u (hu.trans ht) st hu' i⟩

end Uniform.Budget

end NearSquareRoot
end Computability
end OAI
