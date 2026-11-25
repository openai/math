import OAI.Computability.NearSquareRoot.ScheduleStagingProtection
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-!
# The first overflowing digit call in the physical controller

Each canonical digit request either returns its correct tapes inside the
fence or has an actual machine prefix reaching an exterior cell. Successful
earlier requests give a physical path to the first overflowing request.
A successful guarded halt therefore certifies all its digit calls.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingFailure

open IntegerMultiplication TM

variable {A Q I : Type}

def Overflow (m : Rule A Q I) (R : ℕ) (x : Config A Q I) : Prop :=
  ∃ k z j, Trace (advance m) x k z ∧ ((z.tape j).pos < -(R : ℤ) ∨ (R : ℤ) < (z.tape j).pos)

theorem no_overflow_of_fenced_halt {m : Rule A Q I} {R : ℕ} {x y t}
    (h : FencedRun m (fun _ => -(R : ℤ)) (fun _ => R) x t y) (stop : advance m y = none) :
    ¬ Overflow m R x := by
  rintro ⟨k,z,j,run,bad⟩
  have hk := Uniform.before_halt h.1 stop run
  have bounds := h.2 k hk z run j
  exact bad.elim (not_lt_of_ge bounds.1) (not_lt_of_ge bounds.2)

theorem publish_overflow [DecidableEq I] (m : Rule A Q I) (src : I) (decode : A → Option Bool)
    (bit : Bool → A) (blank : A) {R x} (h : Overflow m R x) :
    Overflow (StagingPublish.rule m src decode bit) R (StagingPublish.active blank x) := by
  obtain ⟨k,z,j,run,bad⟩ := h
  exact ⟨k,StagingPublish.active blank z,some j,StagingPublish.lift_run m src decode bit blank run,bad⟩

section Cycle

variable {C D : Type} (g : StagingCycle.Driver A C D I)

/-- Propagate an actual digit prefix through the prior successful calls and
both physical controller phases. No time bound on the failed call is used. -/
theorem first_overflow (R n : ℕ) (init : Config A C I) (row ready : ℕ → Config A C I)
    (reply : ℕ → I → Tape A) (Good : ℕ → Prop)
    (launch : ∃ t, Trace (advance g.controller) init t (row 0))
    (offer : ∀ i < n, ∃ t, Trace (advance g.controller) (row i) t (ready i))
    (pause : ∀ i < n, advance g.controller (ready i) = none ∧ g.paused (ready i).pc = true)
    (success : ∀ i < n, Good i → ∃ q t, Trace (advance g.digit)
      ⟨g.start,(ready i).tape⟩ t ⟨q,reply i⟩ ∧ advance g.digit ⟨q,reply i⟩ = none)
    (recover : ∀ i < n, ∃ t, Trace (advance g.controller) ⟨g.resume,reply i⟩ t (row (i+1)))
    (failure : ∀ i < n, ¬ Good i → Overflow g.digit R ⟨g.start,(ready i).tape⟩) :
    (∀ i < n, Good i) ∨ Overflow g.rule R (StagingCycle.controller init) := by
  classical
  by_cases allGood : ∀ i < n, Good i
  · exact .inl allGood
  right
  push Not at allGood
  let k := Nat.find allGood
  have first := Nat.find_spec allGood
  change k < n ∧ ¬ Good k at first
  have reachable (i : ℕ) (hi : i ≤ k) :
      ∃ t, Trace (advance g.rule) (StagingCycle.controller init) t (StagingCycle.controller (row i)) := by
    induction i with
    | zero =>
      obtain ⟨t,tr⟩ := launch
      exact ⟨t,g.controller_trace tr⟩
    | succ i ih =>
      have hlt : i < k := hi
      have hin := hlt.trans first.1
      obtain ⟨_,path⟩ := ih hlt.le
      obtain ⟨_,out⟩ := offer i hin
      obtain ⟨stop,ok⟩ := pause i hin
      have good : Good i := by
        by_contra bad
        exact Nat.find_min allGood hlt ⟨hin,bad⟩
      obtain ⟨q,_,call,done⟩ := success i hin good
      obtain ⟨_,back⟩ := recover i hin
      exact ⟨_,(((((path.trans (g.controller_trace out)).trans (.single (g.enter _ stop ok))).trans
        (g.digit_trace call)).trans (.single (g.leave _ done))).trans (g.controller_trace back))⟩
  obtain ⟨_,path⟩ := reachable k le_rfl
  obtain ⟨_,out⟩ := offer k first.1
  obtain ⟨stop,ok⟩ := pause k first.1
  obtain ⟨t,z,j,badpath,exterior⟩ := failure k first.1 first.2
  exact ⟨_,StagingCycle.digit z,j,(((path.trans (g.controller_trace out)).trans
    (.single (g.enter _ stop ok))).trans (g.digit_trace badpath)),exterior⟩

end Cycle

open Code Bits ChunkTask ChunkLoop ChunkPhases StagingOuter
open ChunkControl (Driver)

variable {D : Type} (d : Driver) (C : ℕ) (m : Operands → Word) (p : Input)
    (digit : Rule (Letter d) D (Axis d I)) (start : D)

abbrev BadCall (i : ℕ) :=
  Overflow digit (radius C p.n) ⟨start,(request d C m p i).tape⟩

/-- Either every requested digit call has its specified physical result, or
some head of the outer machine actually crosses the common fence. -/
theorem all_calls_or_overflow {T : ℕ} {result : List Ltr}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (compare : ∀ i < p.count, Call d C m p digit start T i ∨ BadCall d C m p digit start i) :
    (∀ i < p.count, Call d C m p digit start T i) ∨
      Overflow (driver d digit start).rule (radius C p.n) (initial d C p) := by
  let row i := atEntry (I:=I) d C p .test (Schoolbook.raw (record m p i))
  let g := driver d digit start
  apply first_overflow g (radius C p.n) p.count _ row (request d C m p) (fun i => (reply d C m p i).tape)
  · obtain ⟨t,_,h⟩ := control_block (I:=I) d C p (StagingBlocks.launch d ctl)
    exact ⟨t,h.1⟩
  · intro i hi
    obtain ⟨t,_,h⟩ := control_block (I:=I) d C p (StagingBlocks.offer d ctl i hi)
    exact ⟨t,h.1⟩
  · intro i _
    exact ⟨mounted_halt d _ _ (StagingControl.pause d _ _),rfl⟩
  · intro i _ h
    obtain ⟨q,t,_,run,stop⟩ := h
    exact ⟨q,t,run.1,stop⟩
  · intro i hi
    obtain ⟨t,_,h⟩ := control_block (I:=I) d C p (StagingBlocks.recover d ctl i hi (width i hi))
    exact ⟨t,h.1⟩
  · intro i hi h
    exact (compare i hi).resolve_left h

theorem outer_or_overflow {T : ℕ} {result : List Ltr}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (compare : ∀ i < p.count, Call d C m p digit start T i ∨ BadCall d C m p digit start i) :
    let g := driver d digit start
    let R := radius C p.n
    (∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8),
      FencedRun g.rule (fun _ => -(R : ℤ)) (fun _ => R) (initial d C p) t (final d C p result) ∧
      advance g.rule (final d C p result) = none) ∨ Overflow g.rule R (initial d C p) :=
  (all_calls_or_overflow d C m p digit start ctl width compare).imp
    (outer d C m p digit start ctl width) id

/-- A protected clear-flag halt forces every digit pair to have returned
its specified result, at every split and for every candidate space bound. -/
theorem calls_of_protected_halt [Finite I] [DecidableEq I] {T t : ℕ} {result : List Ltr} {y}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (compare : ∀ i < p.count, Call d C m p digit start T i ∨ BadCall d C m p digit start i)
    (run : Trace (advance (StagingProtection.rule d digit start)) (StagingProtection.initial d C p.n (input p)) t y)
    (stop : advance (StagingProtection.rule d digit start) y = none) (ok : y.pc.1 = false) :
    ∀ i < p.count, Call d C m p digit start T i := by
  refine (all_calls_or_overflow d C m p digit start ctl width compare).resolve_right ?_
  intro bad
  have publishedBad := publish_overflow _ (StagingOuterOutput.source d) (StagingOuterOutput.decode d)
    (StagingOuterOutput.bit d) (StagingOuterOutput.blank d) bad
  obtain ⟨z,_,good,halt⟩ := StagingProtection.reflect_success d C p.n (input p) digit start run ok stop
  exact no_overflow_of_fenced_halt good halt publishedBad

/-- The actual output of every protected halting success is the specified
word, including when the candidate's a priori space estimate exceeds the
installed fence. -/
theorem protected_output [Finite I] [DecidableEq I] {T t : ℕ} {w : Word} {y}
    (size : w.length = 2*p.n)
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p (w.map Ltr.bit))
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (compare : ∀ i < p.count, Call d C m p digit start T i ∨ BadCall d C m p digit start i)
    (run : Trace (advance (StagingProtection.rule d digit start)) (StagingProtection.initial d C p.n (input p)) t y)
    (stop : advance (StagingProtection.rule d digit start) y = none) (ok : y.pc.1 = false) :
    whole (StagingProtection.blank d) (w.map (StagingProtection.bit d)) (y.tape none) := by
  have allGood := calls_of_protected_halt d C m p digit start ctl width compare run stop ok
  obtain ⟨_,_,z,exec,done,_,out⟩ :=
    StagingProtection.run d C m p w size digit start ctl width allGood
  obtain ⟨_,rfl⟩ := halting_trace_unique run stop exec done
  exact out

end StagingFailure

end NearSquareRoot
end Computability
end OAI
