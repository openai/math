import OAI.Computability.NearSquareRoot.ScheduleInterpreterOutput
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotErase
import OAI.Computability.NearSquareRoot.ScheduleMachineRun
import Batteries.Tactic.OpenPrivate

/-! # Scheduler cursor, unary candidate input, and binary clock tape layout -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotLayout
open IntegerMultiplication TM Timed
open private mapTape from OAI.Computability.NearSquareRoot.ScheduleInterpreterTimed
variable {A Q I : Type} [DecidableEq I]

abbrev Bank (I : Type) := Option (I ⊕ Bool)
abbrev Axis (I : Type) := ScheduleMachine.Index (Bank I)
abbrev Letter (A : Type) := Option Bool × PublishedAttempt.Symbol A

def raw (start : Q) (input : I → Tape A) (idx : I) (blank mark : A) (i : ℕ) : Config A Q I :=
  ⟨start,fun j => if j=idx then
    ⟨0,fun p => if ((RoundExpose.word i 0).view p).isSome then mark else blank⟩ else input j⟩

def clock (a : ℕ) (b : Bool) := RoundExpose.word (if b then a else 0) 0

theorem clock_faithful (a : ℕ) :
    SM.faithful (ScheduleClock.cfg .initialize [] (List.replicate a true)).stack (clock a) := by
  intro b
  cases b
  · exact RoundExpose.faithful_output 0
  · exact RoundExpose.faithful_output a

def tally (idx : I) : Bool → Bank I
  | false => some (.inl idx)
  | true => some (.inr true)

def port (idx : I) : Bool × Bool ↪ Axis I where
  toFun j := if j.2 then .inr (tally idx j.1) else .inl j.1
  inj' := by
    rintro ⟨b,c⟩ ⟨b',c'⟩ h
    cases b <;> cases c <;> cases b' <;> cases c' <;> simp_all [tally]

private def snapshotCell (v : PublishedAttempt.Payload A) (p : ℤ) : PublishedAttempt.Symbol A :=
  ⟨v,v,decide (p=0),decide (p=0),decide (p=0)⟩

def code (blank mark : A) (lit : PublishedAttempt.Symbol A) (l r : ℤ)
    (j : Bool × Bool) (p : ℤ) (v : Option Bool) : PublishedAttempt.Symbol A :=
  if j.2 then snapshotCell (if j.1 then .inr v else
    .inl (if v.isSome then mark else blank,Fence.bits l r p)) p else lit

private def overwrite (blank mark : A) (isClock : Bool) (v : Option Bool)
    (old : PublishedAttempt.Payload A) : PublishedAttempt.Payload A :=
  if isClock then .inr v else old.elim (fun t => .inl (if v.isSome then mark else blank,t.2)) Sum.inr

def write (blank mark : A) (j : Bool × Bool) (v : Option Bool) (c : PublishedAttempt.Symbol A) :
    PublishedAttempt.Symbol A :=
  if j.2 then {c with val := overwrite blank mark j.1 v c.val, fixed := overwrite blank mark j.1 v c.fixed}
  else c

theorem write_code (blank mark : A) (lit : PublishedAttempt.Symbol A) (l r : ℤ)
    (j : Bool × Bool) (p : ℤ) (u v : Option Bool) :
    write blank mark j v (code blank mark lit l r j p u) = code blank mark lit l r j p v := by
  obtain ⟨b,c⟩ := j
  cases b <;> cases c <;> rfl

theorem origin_code (blank mark : A) (lit : PublishedAttempt.Symbol A) (l r : ℤ)
    (b : Bool) (p : ℤ) : (code blank mark lit l r (b,true) p none).origin = decide (p=0) := rfl

def tags (idx : I) (i a : ℕ) (j : Bank I) (p : ℤ) : Option Bool :=
  match j with
  | some (.inl k) => if k=idx then (RoundExpose.word i 0).view p else none
  | some (.inr true) => (RoundExpose.word a 0).view p
  | _ => none

def published (start : Q) (input : I → Tape A) (idx : I) (blank mark : A)
    (lit : PublishedAttempt.Symbol A) (lo hi : I → ℤ) (i a : ℕ) :=
  Release.active lit (Restart.start
    (Attempt.entry lo hi (raw start input idx blank mark i) (clock a)))

def work (start : Q) (input : I → Tape A) (idx : I) (blank mark : A)
    (lit : PublishedAttempt.Symbol A) (lo hi : I → ℤ) (i a : ℕ) :=
  (SlotTracks.dataCfg (tags idx i a) (published start input idx blank mark lit lo hi i a)).tape

def frame (start : Q) (input : I → Tape A) (idx : I) (blank mark : A)
    (lit : PublishedAttempt.Symbol A) (lo hi : I → ℤ) (i a u v : ℕ) :=
  ScheduleMachine.counters (none,lit) (some true,lit) i a (work start input idx blank mark lit lo hi u v)

section
variable (start : Q) (input : I → Tape A) (idx : I) (blank mark : A) (lit : PublishedAttempt.Symbol A)
    (lo hi : I → ℤ)
local notation "F" => frame start input idx blank mark lit lo hi
local notation "C" => code blank mark lit (lo idx) (hi idx)

theorem cursor_eq (i a u v : ℕ) (b : Bool) :
    F i a u v (.inl b) = SlotTracks.tape (C (b,false)) (RoundExpose.cursor (if b then a else i)) := by
  cases b <;> apply congrArg (Tape.mk _) <;> funext d
  · change (if decide ((i : ℤ)+d=0) then (some true,lit) else (none,lit)) =
      ((if decide ((i : ℤ)+d=0) then some true else none),lit)
    cases decide ((i : ℤ)+d=0) <;> rfl
  · change (if decide ((a : ℤ)+d=0) then (some true,lit) else (none,lit)) =
      ((if decide ((a : ℤ)+d=0) then some true else none),lit)
    cases decide ((a : ℤ)+d=0) <;> rfl

theorem tally_eq (i a u v : ℕ) (b : Bool) :
    F i a u v (.inr (tally idx b)) = SlotTracks.tape (C (b,true)) (RoundExpose.word (if b then v else u) 0) := by
  cases b <;>
    simp [frame,ScheduleMachine.counters,ScheduleMachine.mount,work,SlotTracks.dataCfg,SlotTracks.dataTape,
      tags,published,Release.active,Copy.beginCopy,Restart.start,Restart.active,Frontier.config,Frontier.tape,
      Rollback.snapshot,Rollback.origins,Tape.absolute,Attempt.entry,Timed.pack,Fence.marked,Fence.markedTape,
      tally,raw,clock,SlotTracks.tape,code,snapshotCell,mapTape,Tape.loaded]

theorem off_eq (i a u v u' v' : ℕ) (j : Axis I)
    (h : ¬ ∃ b : Bool, .inr (tally idx b) = j) : F i a u v j = F i a u' v' j := by
  cases j with
  | inl => rfl
  | inr j =>
    cases j with
    | none => rfl
    | some j =>
      cases j with
      | inl k =>
        have hne : k ≠ idx := fun e => h ⟨false, by rw [e]; rfl⟩
        simp [frame,ScheduleMachine.counters,ScheduleMachine.mount,work,SlotTracks.dataCfg,
          SlotTracks.dataTape,tags,published,Release.active,Copy.beginCopy,Restart.start,Restart.active,
          Frontier.config,Frontier.tape,Rollback.snapshot,Rollback.origins,Tape.absolute,Attempt.entry,
          Timed.pack,Fence.marked,raw,hne]
      | inr b =>
        cases b with
        | false => rfl
        | true => exact False.elim (h ⟨true,rfl⟩)

end
end Uniform.SlotLayout

end NearSquareRoot
end Computability
end OAI
