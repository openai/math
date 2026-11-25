import OAI.Computability.NearSquareRoot.ScheduleInterpreterRestart

/-!
# A clocked and restartable physical attempt

One fixed transition function performs the guarded interpreter trial and its
physical rollback. On any unsuccessful trial the contents, heads and frontier
bits of every tape, including the clock tapes, return to their entry values.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Attempt

open IntegerMultiplication TM

variable {A Q I : Type}

private def clockAlive : SM.PC Bool ScheduleClock.State Bool → Bool
  | .inl .expired => false
  | _ => true

private theorem clock_isSome (c : ScheduleClock.ClockConfiguration) :
    (advance ScheduleClock.PhysicalRule c).isSome = clockAlive c.pc := by
  obtain ⟨q,T⟩ := c
  cases q with
  | inr pend => rfl
  | inl q =>
    cases q <;> simp only [advance, SM.toTM, ScheduleClock.rule, clockAlive, Option.isSome_map]
    all_goals first | rfl | split <;> rfl

/-- At a stopped trial this finite-control predicate recognizes a completed
candidate and excludes both the clock's timeout and the protected tape abort. -/
def accept (q : (Bool × Q) × SM.PC Bool ScheduleClock.State Bool) : Bool :=
  clockAlive q.2 && !q.1.1

abbrev rule [Fintype I] (blank : A) (m : Rule A Q I) :=
  Restart.rule (Budget.controller blank m) accept

def entry (lo hi : I → ℤ) (x : Config A Q I) (T : Bool → Tape (Option Bool)) :=
  Timed.pack (Fence.marked lo hi false x)
    (⟨.inl .initialize,T⟩ : ScheduleClock.ClockConfiguration)

/-- Exact branch semantics, a bound for the entire physical execution, and
a bound on cells visited through all prefixes. Only a successful branch
leaves tentative output on the working tapes. -/
theorem run [Fintype I] (m : Rule A Q I) (blank : A) (lo hi : I → ℤ) (x : Config A Q I)
    (hx : Fence.within lo hi x) (e : List Bool) (T : Bool → Tape (Option Bool))
    (hf : SM.faithful (ScheduleClock.cfg .initialize [] e).stack T) :
    let src := entry lo hi x T
    let B := Schedule.tryFor (tapeTick (Fence.guard m) (fun q => !q.1))
      (2^e.length) (Fence.marked lo hi false x)
    let space := (∑ i : I, (hi i+1-lo i).toNat) + 2*(e.length+3)
    ∃ t ≤ 10*(e.length+1+6*2^e.length)+4, ∃ w,
      Trace (advance (rule blank m)) (Restart.start src) t w ∧
      advance (rule blank m) w = none ∧
      VisitsAtMost (rule blank m) (Restart.start src) t
        (Fintype.card (I ⊕ Bool) * (2*space+1)) ∧
      ((B = none ∧ w = Restart.retry src) ∨
        ∃ y c l r, B = some y ∧
          w = Restart.active (Frontier.config (Rollback.snapshot src) (Rollback.origins src) l r
            (Timed.pack y c)) ∧
          ∀ i, l i ≤ (src.tape i).pos ∧ (src.tape i).pos ≤ r i ∧
            l i ≤ ((Timed.pack y c).tape i).pos ∧ ((Timed.pack y c).tape i).pos ≤ r i ∧
            r i - l i ≤ ((2*(e.length+1+6*2^e.length) : ℕ) : ℤ)) := by
  obtain ⟨k,kbound,y,c,hist,done,out,space⟩ := Budget.run m blank lo hi x hx e T hf
  obtain ⟨l,r,t,w,interval,ht,physical,halt,whereAt⟩ :=
    Restart.finish (Budget.controller blank m) accept hist done
  refine ⟨t,by omega,w,physical,halt,Restart.visits (Budget.controller blank m) accept hist done space t,?_⟩
  have ok : Timed.answer ScheduleClock.PhysicalRule (fun q : Bool × Q => !q.1) y c =
      if accept (Timed.pack y c).pc then some y else none := by
    simp only [Timed.answer, Timed.pack, accept, clock_isSome]
    rfl
  rw [ok] at out
  cases h : accept (Timed.pack y c).pc with
  | false =>
    exact .inl ⟨by simpa only [h, Bool.false_eq_true, ite_false] using out.symm,
      by simpa only [entry,h,Bool.false_eq_true,ite_false] using whereAt⟩
  | true =>
    refine .inr ⟨y,c,l,r,by simpa only [h, ite_true] using out.symm,
      by simpa only [entry,h,ite_true] using whereAt,?_⟩
    intro i
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := interval i
    exact ⟨h₁,h₂,h₃,h₄,h₅.trans (by exact_mod_cast kbound)⟩

end Uniform.Attempt

end NearSquareRoot
end Computability
end OAI
