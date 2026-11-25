import OAI.Computability.NearSquareRoot.ScheduleRoundControl

/-!
# Fixed physical schedule around a restartable candidate executor

The two counter heads of the schedule are exposed to the executor. The executor
can read their offsets by scanning to the origin marks. Its unsuccessful return
must restore these heads and the reusable work tapes. The combined machine delegates
each executor instruction to the same finite tape transition table, then resumes
the geometric enumeration. An accepting return halts the combined rule in place.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleMachine
open IntegerMultiplication
variable {A Q I : Type}

abbrev Index (I : Type) := Bool ⊕ I
abbrev PC (Q : Type) := RoundControl.State ⊕ Q

private def letter (blank mark : A) (b : Bool) : A := if b then mark else blank

private def mapTape {B C : Type} (g : B → C) (t : TM.Tape B) : TM.Tape C :=
  ⟨t.pos, fun h => g (t.view h)⟩

/-- The extra tapes keep their contents and head positions while the schedule
updates its index and clock exponent. -/
def mount (blank mark : A) (cnt : Bool → TM.Tape Bool) (work : I → TM.Tape A) :
    Index I → TM.Tape A
  | .inl j => mapTape (letter blank mark) (cnt j)
  | .inr j => work j

def counters (blank mark : A) (i a : ℕ) (work : I → TM.Tape A) :=
  mount blank mark (RoundControl.cfg .offer i a).tape work

private def continuation (start : Q) : RoundControl.State → PC Q
  | .offer => .inr start
  | s => .inl s

noncomputable def rule [Finite A] (blank mark : A) (start : Q)
    (trial : TM.Rule A Q (Index I)) (accept : Q → Bool) : TM.Rule A (PC Q) (Index I) := by
  classical
  exact fun pc v =>
    match pc with
    | .inr q =>
      match trial q v with
      | some (q',ops) => some (.inr q',ops)
      | none => if accept q then none else some (.inl .offer, fun j => (v j, .stay))
    | .inl st =>
      let observed := fun j => decide (v (.inl j) = mark)
      (RoundControl.rule st observed).map fun (st',ops) =>
        (continuation start st', fun
          | .inl j => (letter blank mark (ops j).1, (ops j).2)
          | .inr j => (v (.inr j), .stay))

def enter (c : TM.Config A Q (Index I)) : TM.Config A (PC Q) (Index I) :=
  ⟨.inr c.pc, c.tape⟩

def slot (blank mark : A) (start : Q) (work : I → TM.Tape A) (i a : ℕ) :
    TM.Config A (PC Q) (Index I) := ⟨.inr start, counters blank mark i a work⟩

def next (i a : ℕ) : ℕ × ℕ := match a with
  | 0 => (0,i+1)
  | k+1 => (i+1,k)

private theorem mapTape_apply {B C : Type} (g : B → C) (t : TM.Tape B) (op : B × TM.Move) :
    (mapTape g t).apply (g op.1,op.2) = mapTape g (t.apply op) := by
  simp only [mapTape,TM.Tape.apply,TM.Tape.mk.injEq,true_and]
  funext d
  split <;> rfl

private theorem unchanged (t : TM.Tape A) : t.apply (t.view 0,.stay) = t := by
  cases t with
  | mk p f =>
    simp only [TM.Tape.apply,TM.Move.shift,add_zero,TM.Tape.mk.injEq,true_and]
    funext d
    split <;> simp_all

section
variable [Finite A] (blank mark : A) (start : Q) (trial : TM.Rule A Q (Index I)) (accept : Q → Bool)
local notation "M" => rule blank mark start trial accept

theorem run_step {x y : TM.Config A Q (Index I)} (hx : TM.advance trial x = some y) :
    TM.advance M (enter x) = some (enter y) := by
  unfold TM.advance at *
  cases h : trial x.pc (fun j => (x.tape j).view 0) with
  | none => simp [h] at hx
  | some v =>
    rcases v with ⟨q,o⟩
    simp only [h,Option.map_some,Option.some.injEq] at hx
    subst y
    simp [enter, rule, h]

theorem run_lift {x y : TM.Config A Q (Index I)} {t : ℕ} (h : Trace (TM.advance trial) x t y) :
    Trace (TM.advance M) (enter x) t (enter y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (run_step blank mark start trial accept hs) ih

theorem run_fenced {lo hi : Index I → ℤ} {x y : TM.Config A Q (Index I)} {t : ℕ}
    (h : FencedRun trial lo hi x t y) : FencedRun M lo hi (enter x) t (enter y) := by
  refine ⟨run_lift blank mark start trial accept h.1, ?_⟩
  intro k hk c run i
  obtain ⟨z,pre,_⟩ := trace_split h.1 hk
  have e := trace_endpoint_unique run (run_lift blank mark start trial accept pre)
  subst c
  exact h.2 k hk z pre i

theorem finish_accept {x : TM.Config A Q (Index I)} (h : TM.advance trial x = none)
    (ha : accept x.pc = true) : TM.advance M (enter x) = none := by
  unfold TM.advance at *
  have hnone : trial x.pc (fun j => (x.tape j).view 0) = none := by simpa using h
  simp [enter, rule, hnone, ha]

theorem finish_retry {x : TM.Config A Q (Index I)} (h : TM.advance trial x = none)
    (ha : accept x.pc = false) :
    TM.advance M (enter x) = some ⟨.inl .offer, x.tape⟩ := by
  unfold TM.advance at *
  have hnone : trial x.pc (fun j => (x.tape j).view 0) = none := by simpa using h
  simp only [enter, rule, hnone, ha, Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq]
  apply congrArg (TM.Config.mk (A := A) (I := Index I) (Sum.inl RoundControl.State.offer : PC Q))
  exact funext fun j => unchanged (x.tape j)

include blank mark start trial accept in
private theorem control_step (hne : blank ≠ mark) (work : I → TM.Tape A)
    {x y : TM.Config Bool RoundControl.State Bool}
    (h : TM.advance RoundControl.rule x = some y) :
    TM.advance M ⟨.inl x.pc, mount blank mark x.tape work⟩ =
      some ⟨continuation start y.pc, mount blank mark y.tape work⟩ := by
  classical
  have dec (j : Bool) : decide (((mount blank mark x.tape work (.inl j)).view 0) = mark) =
      (x.tape j).view 0 := by
    simp only [mount, mapTape, letter]
    by_cases e : (x.tape j).view 0 = true
    · simp [e]
    · simp [e, hne]
  unfold TM.advance at h ⊢
  cases hx : RoundControl.rule x.pc (fun j => (x.tape j).view 0) with
  | none => simp [hx] at h
  | some v =>
    rcases v with ⟨st,ops⟩
    simp only [hx, Option.map_some, Option.some.injEq] at h
    subst y
    simp only [rule, dec, hx, Option.map_some, Option.some.injEq]
    apply congrArg (TM.Config.mk (continuation start st))
    funext j
    cases j with
    | inl j => exact mapTape_apply (letter blank mark) (x.tape j) (ops j)
    | inr j => exact unchanged (work j)

/-- Loading both counter marks once costs a single physical transition. The work
tapes include the read-only input and whatever fence setup the caller prepared. -/
theorem launch (hne : blank ≠ mark) (work : I → TM.Tape A) :
    TM.advance M ⟨.inl .initialize, mount blank mark RoundControl.initial.tape work⟩ =
      some (slot blank mark start work 0 0) :=
  control_step blank mark start trial accept hne work RoundControl.start

private theorem roll (hne : blank ≠ mark) (work : I → TM.Tape A) (i a : ℕ) :
    Trace (TM.advance M) ⟨.inl .rollover, counters blank mark i a work⟩ (i+1)
      (slot blank mark start work 0 (a+i+1)) := by
  induction i generalizing a with
  | zero =>
    simpa [counters, slot, RoundControl.cfg,continuation] using Trace.single (control_step blank mark start trial accept hne work
      (RoundControl.begin_round a))
  | succ i ih =>
    have fst := control_step blank mark start trial accept hne work (RoundControl.transfer i a)
    have rest := ih (a+1)
    rw [show i+1+1 = 1+(i+1) by omega, show a+(i+1)+1 = a+1+i+1 by omega]
    exact Trace.cons fst rest

/-- The unsuccessful return and movement to the next slot are both charged. -/
theorem retry (hne : blank ≠ mark) (work : I → TM.Tape A) (i a : ℕ)
    {x : TM.Config A Q (Index I)} (restored : x.tape = counters blank mark i a work)
    (h : TM.advance trial x = none) (ha : accept x.pc = false) :
    ∃ t ≤ i+3, Trace (TM.advance M) (enter x) t
      (slot blank mark start work (next i a).1 (next i a).2) := by
  have first := finish_retry blank mark start trial accept h ha
  rw [restored] at first
  cases a with
  | zero =>
    have mid := control_step blank mark start trial accept hne work (RoundControl.enter_rollover i)
    have last := roll blank mark start trial accept hne work i 0
    refine ⟨1+(1+(i+1)),by omega,?_⟩
    simpa [next] using Trace.cons first (Trace.cons mid last)
  | succ a =>
    exact ⟨2,by omega,Trace.cons first (.single (control_step blank mark start trial accept hne work
      (RoundControl.next_slot i a)))⟩

end
end ScheduleMachine

end NearSquareRoot
end Computability
end OAI
