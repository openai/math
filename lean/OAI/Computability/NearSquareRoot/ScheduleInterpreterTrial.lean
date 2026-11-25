import OAI.Computability.NearSquareRoot.Schedule
import OAI.Computability.NearSquareRoot.ScheduleInterpreter
import OAI.Computability.NearSquareRoot.VisitedCells

/-!
# The geometric scheduler's bounded trial on physical tape configurations

A tick consults the finite transition rule once. A stopped run is returned only
when the terminal control state indicates success. The returned configuration
contains the tentative output already written on tape by the candidate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform

open IntegerMultiplication TM

variable {A Q I : Type}

def tapeTick (m : Rule A Q I) (accept : Q → Bool) (x : Config A Q I) :
    Schedule.Tick (Config A Q I) (Config A Q I) :=
  match advance m x with
  | some y => .more y
  | none => if accept x.pc then .done x else .abort

/-- A successful clocked trial contains an actual halting trace. The one
additional tick consults the transition table at its endpoint. -/
theorem tapeTrial_iff (m : Rule A Q I) (accept : Q → Bool) (b : ℕ) (x y : Config A Q I) :
    Schedule.tryFor (tapeTick m accept) b x = some y ↔
      ∃ t < b, Trace (advance m) x t y ∧ advance m y = none ∧ accept y.pc = true := by
  induction b generalizing x with
  | zero => simp [Schedule.tryFor]
  | succ b ih =>
    cases step : advance m x with
    | none =>
      constructor
      · intro h
        cases hg : accept x.pc with
        | false => simp [Schedule.tryFor, tapeTick, step, hg] at h
        | true =>
          obtain rfl : x = y := by simpa [Schedule.tryFor, tapeTick, step, hg] using h
          exact ⟨0, by omega, .nil _, step, hg⟩
      · rintro ⟨t, _, run, halt, ok⟩
        cases run with
        | nil => simp [Schedule.tryFor, tapeTick, step, ok]
        | cons hs => simp [step] at hs
    | some u =>
      simp only [Schedule.tryFor, tapeTick, step, ih]
      constructor
      · rintro ⟨k, hk, hrun, hhalt, hok⟩
        exact ⟨1+k, by omega, .cons step hrun, hhalt, hok⟩
      · rintro ⟨k, hk, hrun, hhalt, hok⟩
        cases hrun with
        | nil => simp [step] at hhalt
        | @cons _ v _ j h' tail =>
          obtain rfl : v = u := Option.some.inj (h'.symm.trans step)
          exact ⟨j, by omega, tail, hhalt, hok⟩

namespace Fence

/-- Crossing a fence can never supply an answer to the scheduler. -/
theorem trial_sound [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ) {x : Config A Q I}
    (hx : within lo hi x) {w : Config (Symbol A) (Bool × Q) I} {b : ℕ}
    (done : Schedule.tryFor (tapeTick (guard m) (fun q => !q.1)) b (marked lo hi false x) =
      some w) :
    ∃ t < b, ∃ y, w = marked lo hi false y ∧ Trace (advance m) x t y ∧ advance m y = none := by
  obtain ⟨t, ht, run, halt, ok⟩ := (tapeTrial_iff _ _ _ _ _).1 done
  exact ⟨t, ht, reflect_halt m lo hi hx run (by simpa using ok) halt⟩

/-- Every confined run completes within one more tick than the number of its
successful physical transitions, independent of the fence width. -/
theorem trial_complete [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    {x y : Config A Q I} {b t : ℕ} (ht : t < b) (run : Trace (advance m) x t y)
    (halt : advance m y = none)
    (fits : ∀ {k c}, k ≤ t → Trace (advance m) x k c → within lo hi c) :
    Schedule.tryFor (tapeTick (guard m) (fun q => !q.1)) b (marked lo hi false x) =
      some (marked lo hi false y) :=
  (tapeTrial_iff _ _ _ _ _).2 ⟨t, ht, trace_marked m lo hi run fits,
    by simp [advance_marked m lo hi y (fits le_rfl run), halt], rfl⟩

/-- The uniform space charge holds for arbitrary cutoffs including rejected
and unfinished trials. It does not depend on the candidate or its time. -/
theorem trial_visited [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ) (x : Config A Q I)
    (hx : within lo hi x) (b : ℕ) :
    VisitsAtMost (guard m) (marked lo hi false x) b (∑ i : I, (hi i + 1 - lo i).toNat) := by
  apply visitsAtMost_of_tape_fences lo hi
  intro k _ w run
  obtain ⟨z, tag, hz, rfl⟩ := trace_within m lo hi hx run
  exact hz

end Fence

end Uniform

end NearSquareRoot
end Computability
end OAI
