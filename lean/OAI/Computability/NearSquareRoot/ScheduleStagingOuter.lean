import OAI.Computability.NearSquareRoot.ScheduleStagingControl
import OAI.Computability.NearSquareRoot.ScheduleStagingBlocks
import OAI.Computability.NearSquareRoot.ScheduleStagingCycle
import OAI.Computability.NearSquareRoot.ScheduleStagingPorts

/-!
# The physical loop around a staged digit call

Only the fixed controller runs between successive digit calls. Each call
receives the complete marked bank at the digit request and returns the same
bank with the reply in register one and every private tape restored. Both
stationary phase changes are charged at every digit pair.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits TM
open ChunkTask ChunkLoop ChunkPhases
open ChunkControl (Driver Phase)
open Schoolbook (raw)

variable {I D : Type} (d : Driver)
abbrev Axis (d : Driver) (I : Type) := StagingPorts.Bank (StagingControl.Axis d) I
abbrev Letter (d : Driver) := StagingReset.Symbol (StagingControl.Letter d)

def radius (C n : ℕ) := 4*(C+50)*(n+1)

def fresh : Option I → Tape (StagingControl.Letter d) := fun _ => Tape.loaded none []

def config {Q : Type} (R : ℕ) (x : Config (StagingControl.Letter d) Q (StagingControl.Axis d)) :
    Config (Letter d) Q (Axis d I) := ⟨x.pc,StagingPorts.marked R x.tape (fresh d)⟩

noncomputable def controller : Rule (Letter d) (StagingControl.State d) (Axis d I) :=
  StagingBank.rule StagingPorts.shelves (StagingPorts.markTrack id id) (StagingControl.rule d)

noncomputable def driver (digit : Rule (Letter d) D (Axis d I)) (beginDigit : D) :
    StagingCycle.Driver (Letter d) (StagingControl.State d) D (Axis d I) where
  controller := controller d
  digit := digit
  start := beginDigit
  resume := .inl (ChunkDispatch.start (StagingOpen.cmd d) .collect)
  paused := StagingControl.digit d

private theorem parked_eq (R : ℕ) {Q : Type} (x : Config (StagingControl.Letter d) Q (StagingControl.Axis d)) :
    StagingBank.parked StagingPorts.shelves (StagingPorts.frame id id (fun _ => rfl) R (fun _ => 0))
      (StagingPorts.marked R x.tape (fresh d (I:=I))) x = config d R x := by
  apply congrArg (Config.mk x.pc)
  funext j
  cases j with
  | inl k =>
    change StagingReset.markedTape R (StagingPorts.imageTape id 0 (x.tape k)) = _
    simp [StagingPorts.imageTape,StagingPorts.marked,StagingPorts.split]
  | inr k => rfl

private theorem parked_on (R : ℕ) {Q : Type} (x y : Config (StagingControl.Letter d) Q (StagingControl.Axis d)) :
    StagingBank.parked StagingPorts.shelves (StagingPorts.frame id id (fun _ => rfl) R (fun _ => 0))
      (StagingPorts.marked R x.tape (fresh d (I:=I))) y = config d R y := by
  trans StagingBank.parked StagingPorts.shelves (StagingPorts.frame id id (fun _ => rfl) R (fun _ => 0))
    (StagingPorts.marked R y.tape (fresh d)) y
  · apply congrArg (Config.mk y.pc)
    funext j
    cases j <;> rfl
  · exact parked_eq d R y

private theorem mounted_run {R : ℕ} {x y : Config _ (StagingControl.State d) (StagingControl.Axis d)} {t}
    (run : Trace (advance (StagingControl.rule d)) x t y) :
    Trace (advance (controller d (I:=I))) (config d R x) t (config d R y) := by
  have h := StagingBank.run StagingPorts.shelves (StagingPorts.markTrack id id)
    (StagingPorts.frame id id (fun _ => rfl) R (fun _ => 0))
    (StagingPorts.marked R x.tape (fresh d (I:=I))) (StagingControl.rule d) run
  simpa only [controller,parked_on] using h

theorem mounted_halt (R : ℕ) (x : Config _ (StagingControl.State d) (StagingControl.Axis d))
    (stop : advance (StagingControl.rule d) x = none) :
    advance (controller d (I:=I)) (config d R x) = none := by
  have h := StagingBank.halt StagingPorts.shelves (StagingPorts.markTrack id id)
    (StagingPorts.frame id id (fun _ => rfl) R (fun _ => 0))
    (StagingPorts.marked R x.tape (fresh d (I:=I))) (StagingControl.rule d) stop
  simpa only [controller,parked_eq] using h

private theorem bottom_range (C : ℕ) (p : Input) (j : StagingControl.Axis d) :
    let H := (C+34)*(p.n+1)
    let B := StagingControl.initialBottom d (input p) j
    (-(radius C p.n : ℤ) ≤ B-H-1) ∧ B+1 ≤ radius C p.n := by
  have hs := input_length p
  have big : (C+34)*(p.n+1)+32*(p.n+1)+1 ≤ radius C p.n := by
    unfold radius
    nlinarith
  dsimp only [StagingControl.initialBottom]
  split <;> omega

theorem control_block (C : ℕ) (p : Input) {x y : ChunkDispatch.Config (StagingOpen.cmd d)}
    {cost : ℕ} (h : StagingBlocks.Block d x y cost ((C+34)*(p.n+1))) :
    let B := StagingControl.initialBottom d (input p)
    let R := radius C p.n
    ∃ t ≤ 2*cost, FencedRun (controller d (I:=I)) (fun _ => -(R : ℤ)) (fun _ => R)
      (config d R (StagingControl.physical B x)) t (config d R (StagingControl.physical B y)) := by
  obtain ⟨t,ht,run⟩ := StagingControl.block d h (StagingControl.initialBottom d (input p))
  refine ⟨t,ht,mounted_run d run.1,fun u hu z hz j => ?_⟩
  obtain ⟨w,hw,_⟩ := trace_split run.1 hu
  rw [trace_endpoint_unique hz (mounted_run d hw)]
  cases j with
  | inl j =>
    have hh := run.2 u hu w hw j
    have bounds := bottom_range d C p j
    exact ⟨bounds.1.trans hh.1,hh.2.trans bounds.2⟩
  | inr j =>
    change -(radius C p.n : ℤ) ≤ 0 ∧ 0 ≤ (radius C p.n : ℤ)
    omega

variable (C : ℕ) (m : Operands → Word) (p : Input)

noncomputable abbrev atEntry (f : Phase) (r : Reg Ltr) :=
  config (I:=I) d (radius C p.n) (StagingControl.entry d (StagingControl.initialBottom d (input p)) f r)

noncomputable abbrev initial := StagingCycle.controller (D := D) (atEntry (I:=I) d C p .load (raw (input p)))

noncomputable abbrev final (result : List Ltr) := StagingCycle.controller (D := D)
  (config (I:=I) d (radius C p.n)
    (StagingControl.returned d (StagingControl.initialBottom d (input p)) .emit (raw result)))

noncomputable abbrev request (i : ℕ) := atEntry (I:=I) d C p .digit
  (StagingPhases.slot (p.bundle m i) (StagingPhases.request (digitQuery m p i)))

noncomputable abbrev reply (i : ℕ) := atEntry (I:=I) d C p .collect
  (StagingPhases.slot (p.bundle m i) ((digitReply m p i).map Ltr.bit))

theorem initial_tapes :
    (initial (I:=I) (D:=D) d C p).tape =
      StagingPorts.marked (radius C p.n)
        (fun j => if j = ChunkDispatch.output (StagingOpen.cmd d) then
          Tape.loaded none (((input p).map Sum.inl).map some) else Tape.loaded none []) (fresh d) := by
  change StagingPorts.marked _ (StagingControl.entry d _ .load _).tape _ = _
  rw [StagingControl.entry_input]

theorem final_register (result : List Ltr) :
    (final (D:=D) (I:=I) d C p result).tape (.inl (ChunkDispatch.output (StagingOpen.cmd d))) =
      StagingReset.markedTape (radius C p.n)
        (StagingControl.tape ((input p).length : ℤ) (result.map Sum.inl)) := by
  change StagingReset.markedTape _
    (StagingControl.tape (StagingControl.initialBottom d (input p) _) _) = _
  simp only [StagingControl.initialBottom,ite_true]
  rfl

/-- All parked shelves fit the digit-stage fence already at the moment the
query is exposed, independently of the digit program's resource bounds. -/
theorem request_heads (i : ℕ) (hi : i < p.count) (j : StagingControl.Axis d) :
    let B := StagingControl.initialBottom d (input p)
    let shelves := (StagingControl.entry d B .digit
      (StagingPhases.slot (p.bundle m i) (StagingPhases.request (digitQuery m p i)))).tape
    (-(radius C p.n : ℤ) ≤ (shelves j).pos) ∧ (shelves j).pos ≤ radius C p.n := by
  let regs := StagingPhases.slot (p.bundle m i) (StagingPhases.request (digitQuery m p i))
  let x := ChunkDispatch.beginPhase (StagingOpen.cmd d) .digit regs
  have h : (x.stack j).length ≤ 32*(p.n+1) :=
    ChunkDispatch.begin_height _ _ _ _ (StagingPhases.request_height m p i hi.le) j
  have hh : 32*(p.n+1) ≤ (C+34)*(p.n+1) := Nat.mul_le_mul_right _ (by omega)
  have bounds := bottom_range d C p j
  change -(radius C p.n : ℤ) ≤ StagingControl.initialBottom d (input p) j-((x.stack j).length : ℤ) ∧
    StagingControl.initialBottom d (input p) j-((x.stack j).length : ℤ) ≤ radius C p.n
  dsimp only at bounds
  omega

/-- Exact bank contract for a single physical digit computation. -/
def Call (digit : Rule (Letter d) D (Axis d I)) (beginDigit : D) (T i : ℕ) : Prop :=
  let R := radius C p.n
  ∃ q : D, ∃ t ≤ T, FencedRun digit (fun _ => -(R : ℤ)) (fun _ => R)
    ⟨beginDigit,(request d C m p i).tape⟩ t ⟨q,(reply d C m p i).tape⟩ ∧
    advance digit ⟨q,(reply d C m p i).tape⟩ = none

/-- Execute the fixed controller to completion, including every digit call,
with a single absolute radius for all phases and all digit pairs. -/
theorem outer (digit : Rule (Letter d) D (Axis d I)) (beginDigit : D) {T : ℕ} {result : List Ltr}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (call : ∀ i < p.count, Call d C m p digit beginDigit T i) :
    let g := driver d digit beginDigit
    let R := radius C p.n
    ∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8),
      FencedRun g.rule (fun _ => -(R : ℤ)) (fun _ => R) (initial d C p) t (final d C p result) ∧
      advance g.rule (final d C p result) = none := by
  classical
  let g := driver d digit beginDigit
  let R := radius C p.n
  let B := C*(p.n+1)
  let row i := atEntry (I:=I) d C p .test (raw (record m p i))
  let endPC (i : ℕ) := if h : i < p.count then (call i h).choose else beginDigit
  let got (i : ℕ) : Config (Letter d) D (Axis d I) := ⟨endPC i,(reply d C m p i).tape⟩
  have digit_runs (i : ℕ) (hi : i < p.count) :
      ∃ t ≤ T, FencedRun g.digit (fun _ => -(R : ℤ)) (fun _ => R)
        ⟨g.start,(request d C m p i).tape⟩ t (got i) ∧ advance g.digit (got i) = none := by
    simpa only [g,driver,R,got,endPC,dite_eq_left hi] using (call i hi).choose_spec
  obtain ⟨t,ht,run,stop⟩ := g.run_fenced row (request d C m p) got p.count
    (control_block d C p (StagingBlocks.launch d ctl))
    (fun i hi => control_block d C p (StagingBlocks.offer d ctl i hi))
    (fun i _ => ⟨mounted_halt d R _ (StagingControl.pause d _ _), rfl⟩) digit_runs
    (fun i hi => control_block d C p (StagingBlocks.recover d ctl i hi (width i hi)))
    (control_block d C p (StagingBlocks.complete d ctl))
    (mounted_halt d R _ (StagingControl.finished d _ _)) rfl
  refine ⟨t,ht.trans ?_,run,stop⟩
  change 2*(B+1)+p.count*(2*(2*B+2)+T+2*(B+1)+2)+2*(2*B+1) ≤
    (p.count+1)*(6*B+T+8)
  rw [Nat.add_mul]
  rw [show 2*(2*B+2)+T+2*(B+1)+2 = 6*B+T+8 by omega]
  omega

end StagingOuter

end NearSquareRoot
end Computability
end OAI
