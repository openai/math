import OAI.Computability.NearSquareRoot.ScheduleStagingStartupRoute

/-! # From a literal pair to the call-ready physical workspace

The initialization executes the split check, copies the serialized request,
generates the radius, installs both marker layers, and hands off at the
prescribed control state. Every intermediate state counts towards its clock.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingStartup

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open StagingProtection (Cell Tapes)

variable {I P Q A X Y : Type} (d : Driver)

private theorem sequence {m : Rule A P I} {n : Rule A Q I} {x y : Config A P I} {v w : Config A Q I}
    {t s : ℕ} (h : Trace (advance m) x t y) (halt : advance m y = none)
    (g : Trace (advance n) v s w) (stop : advance n w = none) (same : v.tape = y.tape) :
    let r := TapeSequence.rule m n v.pc
    Trace (advance r) (TapeSequence.relabel Sum.inl x) (t+1+s) (TapeSequence.relabel Sum.inr w) ∧
      advance r (TapeSequence.relabel Sum.inr w) = none := by
  apply TapeSequence.run m n v.pc h halt _ stop
  simpa only [← same] using g

variable [DecidableEq I] [DecidableEq (StagingControl.Letter d)]

abbrev prepRule (k C : ℕ) : Rule (Cell d) (PC k (StagingWidth.Phase C)) (Axis d I) :=
  prelude d k (StagingWidth.rule d C) (StagingWidth.start C) (StagingWidth.delimiter d)

def sourceAt (x y : Word) : Tape (Cell d) :=
  Reset.atHead x.length (StagingSerialize.content d (StagingSerialize.raw x y))

def budget (C n : ℕ) := (24*(C+50)+77)*(n+1)

/-- The bounded trace ends on exactly the protected work tapes used by the
staged program. The two startup tapes are parked at explicitly known heads. -/
theorem prepares (C : ℕ) (p : ChunkTask.Input) :
    let dst := prepared d p.k C p.n (ChunkPhases.input p) (sourceAt d p.x p.y) (StagingWidth.widthTape d C p.n)
    ∃ t ≤ budget C p.n, Trace (advance (prepRule d (I:=I) p.k C)) (initial d p.k p.x p.y) t dst ∧
      advance (prepRule d p.k C) dst = none := by
  let s := ChunkPhases.input p
  let W := StagingWidth.first d C p.n ++ [StagingWidth.delimiter d]
  let width := StagingWidth.widthTape d C p.n
  let source := sourceAt d p.x p.y
  let r := inputRoute (inputReg d (I:=I))
  let r' := publicRoute (Tapes d I)
  let b := blankTape d
  let park := particles d (I:=I) s
  let orig := store (rawTape d p.x p.y) b park
  let last := store source width park
  obtain ⟨t,ht,first,fhalt⟩ := StagingSerialize.run d p
  let x := mapper r (fun _ => b) (StagingSerialize.initial d p.k p.x p.y)
  let y := mapper r (fun _ => b) (StagingSerialize.ready d p)
  have fst : Trace (advance (r.rule (serial d p.k))) x t y :=
    mapped_trace _ _ _ (serial_trace d p.k first)
  have fstop : advance (r.rule (serial d p.k)) y = none := by
    rw [show y = mapper r (fun _ => b) (StagingSerialize.ready d p) from rfl,mapped_step]
    rfl
  obtain ⟨wh,whalt⟩ := StagingWidth.run d C p.x p.y
  let v := mapper r' orig (StagingWidth.initial d C p.x p.y)
  let w := mapper r' orig (StagingWidth.doneConfig d C p.x p.y)
  have second := mapped_trace r' orig _ wh
  have wstop : advance (r'.rule (StagingWidth.rule d C)) w = none := by
    dsimp only [w]; rw [mapped_step,whalt]; rfl
  have same : v.tape = y.tape := by
    rw [show y.tape = orig from after_serial d p]
    funext i
    rcases i with (_|_)|j <;> rfl
  obtain ⟨double,stop₂⟩ := sequence fst fstop second wstop same
  have hh := StagingMarks.install d (StagingWidth.delimiter d) (StagingWidth.first d C p.n) []
    (StagingMarks.words d (I:=I) s) (StagingWidth.first_delim d C p.n) (StagingWidth.first_blank d C p.n) (by simp [StagingWidth.delimiter])
  rw [StagingWidth.first_length] at hh
  obtain ⟨hmarks,haltMarks⟩ := hh
  let a := StagingMarks.before d W (StagingMarks.words d (I:=I) s)
  let z := StagingMarks.image d (ChunkGuard.afterInit none W (StagingMarks.words d (I:=I) s) (StagingProtection.Rpub C p.n))
  let mr := StagingMarks.rule d (I:=I) (StagingWidth.delimiter d)
  let θ := markRoute d (I:=I)
  have third : Trace (advance (θ.rule mr)) (mapper θ last a) (4*StagingProtection.Rpub C p.n+7)
      (mapper θ last z) := mapped_trace _ _ _ hmarks
  have endH : advance (θ.rule mr) (mapper θ last z) = none := by rw [mapped_step,haltMarks]; rfl
  have glued : (mapper θ last a).tape = (TapeSequence.relabel Sum.inr w : Config _ (StagingSerialize.Phase p.k ⊕ _) _).tape := by
    have eq := marks_before (I:=I) d s source W
    change (mapper θ last a).tape = w.tape
    rw [show (mapper θ last a).tape = last from eq]
    funext i
    rcases i with (_|_)|j <;> rfl
  obtain ⟨all,stop⟩ := sequence double stop₂ third endH glued
  have firstEq : TapeSequence.relabel Sum.inl (TapeSequence.relabel Sum.inl x) =
      initial (P:=StagingWidth.Phase C) d p.k p.x p.y := by
    change Config.mk _ _ = Config.mk _ _
    rw [Config.mk.injEq]
    exact ⟨rfl,begin_serial (P:=StagingWidth.Phase C) d p.k p.x p.y⟩
  have lastEq : TapeSequence.relabel Sum.inr (mapper θ last z) =
      prepared (P:=StagingWidth.Phase C) d p.k C p.n s source width := by
    change Config.mk _ _ = Config.mk _ _
    rw [Config.mk.injEq]
    exact ⟨rfl,marks_after (P:=StagingWidth.Phase C) d p.k C p.n s source W⟩
  change Trace (advance (prepRule d p.k C)) _ _ _ at all
  rw [firstEq,lastEq] at all
  rw [lastEq] at stop
  refine ⟨_,?_,all,stop⟩
  change t+1+(2*StagingProtection.Rpub C p.n+p.n+3)+1+
    (4*StagingProtection.Rpub C p.n+7) ≤ budget C p.n
  unfold budget StagingProtection.Rpub StagingOuter.radius
  nlinarith

end StagingStartup

end NearSquareRoot
end Computability
end OAI
