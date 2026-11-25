import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotOrigins
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotLift
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotDispatch

/-!
# One restarting scheduler executor, from a single indexed candidate machine

The candidate receives its index in unary on an ordinary data tape. Generation
and interpretation of the indexed code run under the binary budget clock.
At an unsuccessful return the input, both scheduler cursors, all scratch
tapes, and every absolute fence and snapshot mark equal their entry values.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot
open IntegerMultiplication TM SlotLayout
variable {A Q I : Type} [Fintype I] [DecidableEq I]

abbrev TrialPC (Q I : Type) :=
  Release.Control (Restart.Control ((Bool × Q) × SM.PC Bool ScheduleClock.State Bool) (I ⊕ Bool))
abbrev PC (Q I : Type) := SlotDispatch.PC Prep (TrialPC Q I) Prep

def trialStart (start : Q) : TrialPC Q I := .inl (.inl (.inl ((false,start),.inl .initialize)))
def entry : PC Q I := .inl (.inl .scan)
def accepted : PC Q I → Bool := SlotDispatch.accepted PublishedAttempt.accepted

noncomputable def executor (m : Rule A Q I) (start : Q) (idx src : I) (blank mark : A)
    (decode : A → Option Bool) (bit : Bool → PublishedAttempt.Symbol A) : Rule (Letter A) (PC Q I) (Axis I) :=
  SlotDispatch.rule (prepare idx blank mark)
    (SlotLift.trial (PublishedAttempt.rule m blank src decode bit)) (remove idx blank mark)
    (trialStart start) (.inl .scan) PublishedAttempt.accepted

def answer (m : Rule A Q I) (start : Q) (input : I → Tape A) (idx : I) (blank mark : A)
    (lo hi : I → ℤ) (i budget : ℕ) :=
  Schedule.tryFor (tapeTick (Fence.guard m) (fun q => !q.1)) budget
    (Fence.marked lo hi false (raw start input idx blank mark i))

/-- A concrete instance of the per-slot scheduler interface. The input layout
and static fence widths depend only on the original multiplication input. -/
theorem slots [Finite A] (m : Rule A Q I) (start : Q) (input : I → Tape A)
    (idx src : I) (distinct : src ≠ idx) (blank mark : A) (rawBit : Bool → A)
    (lit : PublishedAttempt.Symbol A) (bit : Bool → PublishedAttempt.Symbol A)
    (decode : A → Option Bool) (empty : decode blank = none) (digits : ∀ b, decode (rawBit b) = some b)
    (lo hi : I → ℤ) (inputOrigin : ∀ j, (input j).pos = 0) (fits : ∀ j, lo j ≤ 0 ∧ 0 ≤ hi j)
    (pristine : (input src).absolute = fun _ => blank) (P : List Bool → Prop) (N : ℕ)
    (i a : ℕ) (correct : ∀ {t y}, Trace (advance m) (raw start input idx blank mark i) t y →
      advance m y = none → ∃ z : List Bool, z.length ≤ N ∧ P z ∧ whole blank (z.map rawBit) (y.tape src)) :
    let R := SlotCost.radius I (∑ j, (hi j+1-lo j).toNat) N i a
    ScheduleMachine.AttemptReturns (none,lit) (some true,lit) entry
      (executor m start idx src blank mark decode bit) accepted
      (work start input idx blank mark lit lo hi 0 0) (fun _ => -(R : ℤ)) (fun _ => R)
      (fun _ y => ∃ z, P z ∧ whole (none,lit) (z.map fun b => (none,bit b)) (y.tape (.inr none)))
      (answer m start input idx blank mark lo hi) (fun j e => 120*(2^e+j+e+1)) i a := by
  let x := raw start input idx blank mark i
  let p := published start input idx blank mark lit lo hi i a
  let M := PublishedAttempt.rule m blank src decode bit
  let F := frame start input idx blank mark lit lo hi i a
  let W := ∑ j, (hi j+1-lo j).toNat
  let S := SlotCost.space I W a
  let U := S+1+Fintype.card (Bank I)*(8*S+2*N+7)
  let R := SlotCost.radius I W N i a
  let e := List.replicate a true
  let V := tags idx i a
  let mount := SlotLift.mount (Q := TrialPC Q I) (F i a) V
  have origin := raw_origins start input idx blank mark inputOrigin i
  have within : Fence.within lo hi x := fun j => by dsimp only [x]; rw [origin]; exact fits j
  have zero : (x.tape src).absolute = fun _ => blank := by simpa [x,raw,distinct] using pristine
  obtain ⟨t,ht,y,tr,stop,cells,branch⟩ := PublishedAttempt.slot m blank rawBit src lo hi x within
    (origin src) e (clock a) zero (clock_faithful a) decode empty digits lit bit P N (fun h k => correct h k)
  have elen : e.length = a := List.length_replicate
  rw [elen] at ht cells branch
  change Trace (advance M) p t y at tr
  change VisitsAtMost M p t U at cells
  change (answer m start input idx blank mark lo hi i (2^a) = none ∧ _ ∧ y.tape=p.tape) ∨
    ((answer m start input idx blank mark lo hi i (2^a)).isSome ∧ _ ∧ _) at branch
  have room : 3*(i+a)+5 ≤ R := Nat.le_max_left _ _
  have fitsU : U ≤ R := Nat.le_max_right _ _
  have init : mount p = ⟨trialStart start,F i a⟩ :=
    SlotLift.mount_start start input idx blank mark lit lo hi i a
  obtain ⟨mid,halt⟩ := SlotLift.fenced_run M (F i a) V tr stop cells fitsU
    (published_origins start input idx blank mark lit lo hi inputOrigin i a)
    (SlotLift.cursor_range start input idx blank mark lit lo hi i a R (by omega) (by omega))
  change FencedRun _ _ _ (mount p) t (mount y) at mid
  rw [init] at mid
  obtain ⟨pre,prehalt⟩ := prepare_run start input idx blank mark lit lo hi i a
  have preF := tally_fenced start input idx blank mark lit lo hi _ inputOrigin i a 0 0 pre room
  have charge := SlotCost.time_le i a
  rcases branch with ⟨bad,reject,restored⟩ | ⟨ok,accept,z,hz,output⟩
  · have restore : (mount y).tape = F i a :=
      SlotLift.mount_reject start input idx blank mark lit lo hi i a y restored
    obtain ⟨clean,cleanhalt⟩ := remove_run start input idx blank mark lit lo hi i a
    have cleanF := tally_fenced start input idx blank mark lit lo hi _ inputOrigin i a i a clean room
    change FencedRun (remove idx blank mark) _ _ ⟨.inl .scan,F i a⟩ _ _ at cleanF
    rw [←restore] at cleanF
    obtain ⟨run,done⟩ := SlotDispatch.run_retry _ _ _ _ _ PublishedAttempt.accepted preF prehalt mid
      halt reject cleanF cleanhalt
    refine ⟨_,_,by dsimp only; omega,run,done,?_⟩
    rw [bad]
    exact ⟨rfl,rfl⟩
  · obtain ⟨run,done⟩ := SlotDispatch.run_accept _ _ _ _ (.inl .scan : Prep)
      PublishedAttempt.accepted preF prehalt mid halt accept
    refine ⟨_,_,by dsimp only; omega,run,done,?_⟩
    cases h : answer m start input idx blank mark lo hi i (2^a) with
    | none => simp [h] at ok
    | some v =>
      refine ⟨accept,z,hz,?_⟩
      exact SlotLift.mount_output (F i a) V lit bit z (fun _ => rfl) output

end Uniform.IndexedSlot

end NearSquareRoot
end Computability
end OAI
