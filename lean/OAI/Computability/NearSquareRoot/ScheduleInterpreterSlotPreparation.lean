import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotLayout

/-! # Physical preparation and retraction of both unary slot parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotLayout
open IntegerMultiplication TM
variable {A Q I : Type} [DecidableEq I]

abbrev Prep := RoundExpose.State ⊕ RoundExpose.State

noncomputable def prepare (idx : I) (blank mark : A) : Rule (Letter A) Prep (Axis I) :=
  CommonTapes.rule (port idx) (SlotTracks.rule (write blank mark) RoundExpose.bothRule)

def one (idx : I) (b : Bool) : Unit ↪ Axis I where
  toFun _ := .inr (tally idx b)
  inj' := fun _ _ _ => Subsingleton.elim _ _

noncomputable def removeOne (idx : I) (blank mark : A) (b : Bool) :
    Rule (Letter A) SlotErase.State (Axis I) :=
  CommonTapes.rule (one idx b) (SlotErase.rule (write blank mark (b,true) none) Reset.Cell.origin)

noncomputable def remove (idx : I) (blank mark : A) : Rule (Letter A) Prep (Axis I) :=
  TapeSequence.rule (removeOne idx blank mark false) (removeOne idx blank mark true) .scan

theorem extend_eq {B J K : Type} (e : J ↪ K) (f : J → B) (other g : K → B)
    (onPort : ∀ j, f j = g (e j)) (offPort : ∀ k, (¬∃ j, e j=k) → other k=g k) :
    CommonTapes.extend e f other = g := by
  funext k
  by_cases h : ∃ j, e j = k
  · obtain ⟨j,rfl⟩ := h
    rw [CommonTapes.extend_apply,onPort]
  · rw [CommonTapes.extend_off e _ _ _ h,offPort _ h]

variable (start : Q) (input : I → Tape A) (idx : I) (blank mark : A) (lit : PublishedAttempt.Symbol A)
    (lo hi : I → ℤ)
local notation "F" => frame start input idx blank mark lit lo hi
local notation "C" => code blank mark lit (lo idx) (hi idx)

private theorem prepare_mount (i a : ℕ) (filled : Bool) :
    let u := if filled then i else 0
    let v := if filled then a else 0
    let x := if filled then RoundExpose.bothDone i a else RoundExpose.bothStart i a
    (CommonTapes.config (port idx) (F i a 0 0) (SlotTracks.cfg C x)).tape = F i a u v := by
  dsimp only
  apply extend_eq
  · rintro ⟨b,c⟩
    cases c
    · rw [show port idx (b,false) = Sum.inl b by rfl,cursor_eq]
      cases filled <;> cases b <;> rfl
    · rw [show port idx (b,true) = Sum.inr (tally idx b) by rfl,tally_eq]
      cases filled <;> cases b <;> rfl
  · intro j hj
    apply off_eq
    rintro ⟨b,rfl⟩
    exact hj ⟨(b,true),rfl⟩

theorem prepare_run (i a : ℕ) :
    Trace (advance (prepare idx blank mark)) ⟨.inl .scan,F i a 0 0⟩ (2*(i+a)+5)
      ⟨.inr .done,F i a i a⟩ ∧ advance (prepare idx blank mark) ⟨.inr .done,F i a i a⟩ = none := by
  let x := RoundExpose.bothStart i a
  let y := RoundExpose.bothDone i a
  let lift := fun (z : Config _ Prep _) =>
    CommonTapes.config (port idx) (F i a 0 0) (SlotTracks.cfg C z)
  have hx : lift x = ⟨.inl .scan,F i a 0 0⟩ :=
    congrArg (Config.mk _) (prepare_mount start input idx blank mark lit lo hi i a false)
  have hy : lift y = ⟨.inr .done,F i a i a⟩ :=
    congrArg (Config.mk _) (prepare_mount start input idx blank mark lit lo hi i a true)
  rw [←hx,←hy]
  refine ⟨CommonTapes.trace _ _ _ (SlotTracks.trace _ _ _
    (write_code blank mark lit (lo idx) (hi idx)) (RoundExpose.expose_both i a).1),?_⟩
  unfold lift prepare
  rw [CommonTapes.advance_config,SlotTracks.advance_cfg _ _ _ (write_code blank mark lit (lo idx) (hi idx)),RoundExpose.both_halt]
  rfl

private theorem remove_one (i a u v : ℕ) (b : Bool) :
    let n := if b then v else u
    let g := F i a (if b then u else 0) (if b then 0 else v)
    Trace (advance (removeOne idx blank mark b)) ⟨.scan,F i a u v⟩ (2*n+2) ⟨.done,g⟩ ∧
      advance (removeOne idx blank mark b) ⟨.done,g⟩ = none := by
  let n := if b then v else u
  let g := F i a (if b then u else 0) (if b then 0 else v)
  let e := one idx b
  let M := SlotErase.rule (write blank mark (b,true) none) Reset.Cell.origin
  let x : Config _ SlotErase.State Unit := ⟨.scan,fun _ => SlotTracks.tape (C (b,true)) (RoundExpose.word n 0)⟩
  let y : Config _ SlotErase.State Unit := ⟨.done,fun _ => SlotTracks.tape (C (b,true)) (RoundExpose.word 0 0)⟩
  let lift := CommonTapes.config (Q := SlotErase.State) e (F i a u v)
  have hx : lift x = ⟨.scan,F i a u v⟩ := by
    apply congrArg (Config.mk _)
    apply extend_eq
    · intro; exact (tally_eq start input idx blank mark lit lo hi i a u v b).symm
    · intro _ _; rfl
  have hy : lift y = ⟨.done,g⟩ := by
    apply congrArg (Config.mk _)
    apply extend_eq
    · intro k
      cases b
      · exact (tally_eq start input idx blank mark lit lo hi i a 0 v false).symm
      · exact (tally_eq start input idx blank mark lit lo hi i a u 0 true).symm
    · intro j h
      by_cases hh : ∃ c : Bool, Sum.inr (tally idx c) = j
      · obtain ⟨c,rfl⟩ := hh
        have ne : b ≠ c := fun he => h ⟨(),by rw [←he];rfl⟩
        dsimp only [g]
        rw [tally_eq,tally_eq]
        cases b <;> cases c <;> simp_all
      · exact off_eq start input idx blank mark lit lo hi _ _ _ _ _ _ _ hh
  change Trace (advance (CommonTapes.rule e M)) _ _ _ ∧ _
  rw [←hx,←hy]
  refine ⟨CommonTapes.trace _ _ _ (SlotErase.erase _ _ _ (fun p d => write_code _ _ _ _ _ _ p d none)
    (origin_code blank mark lit (lo idx) (hi idx) b) n),?_⟩
  change advance (CommonTapes.rule e M) (CommonTapes.config e (F i a u v) y) = none
  rw [CommonTapes.advance_config]
  rfl

theorem remove_run (i a : ℕ) :
    Trace (advance (remove idx blank mark)) ⟨.inl .scan,F i a i a⟩ (2*(i+a)+5)
      ⟨.inr .done,F i a 0 0⟩ ∧ advance (remove idx blank mark) ⟨.inr .done,F i a 0 0⟩ = none := by
  obtain ⟨first,hfirst⟩ := remove_one start input idx blank mark lit lo hi i a i a false
  obtain ⟨second,hsecond⟩ := remove_one start input idx blank mark lit lo hi i a 0 a true
  rw [show 2*(i+a)+5=(2*i+2)+1+(2*a+2) by omega]
  exact TapeSequence.run _ _ .scan first hfirst second hsecond

end Uniform.SlotLayout

end NearSquareRoot
end Computability
end OAI
