import OAI.Computability.NearSquareRoot.CommonAlphabetAlign

/-! # Returning the physical output head and clearing its distance counter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM

variable {A Q I : Type} [DecidableEq I]

/-- Reposition just the designated output head over the original absolute contents. -/
def outputAt (out : I) (x : Config A Q I) (p : ℤ) (i : I) : Tape A :=
  if i = out then Reset.atHead p (x.tape out).absolute else x.tape i

def ret (out : I) (blank marker : A) (neg : Bool) (x : Config A Q I) (n : ℕ) :
    Config A (Phase Q) (Option I) :=
  ⟨.rewind neg, banks (outputAt out x (side neg n)) (counter blank marker n)⟩

def final (out : I) (blank : A) (x : Config A Q I) : Config A (Phase Q) (Option I) :=
  ⟨.done, banks (outputAt out x 0) (Tape.loaded blank [])⟩

private theorem readMove (p : ℤ) (f : ℤ → A) (d : Move) :
    (Reset.atHead p f).apply ((Reset.atHead p f).view 0,d) = Reset.atHead (p+d.shift) f := by
  change (Reset.atHead p f).apply (f (p+0),d) = _
  rw [add_zero,Reset.atHead_apply,Function.update_eq_self]

variable [DecidableEq A] (out : I) (blank marker : A) (entry : Q) (m : Rule A Q I)
local notation "M" => rule out blank marker entry m

/-- The first physical transition following a candidate halt selects output rewind. -/
theorem dispatch (neg : Bool) (x : Config A Q I) (halt : advance m x = none)
    (sign : (x.tape out).pos ≠ 0 → neg = decide ((x.tape out).pos < 0)) :
    advance M (running out blank marker neg x) =
      some (ret out blank marker neg x (x.tape out).pos.natAbs) := by
  simp [advance] at halt
  unfold advance rule running
  simp only [banks, halt, Option.map_some, Option.some.injEq]
  simp only [ret, Config.mk.injEq, true_and]
  funext i
  cases i with
  | none => exact stay _
  | some i =>
    simp only [banks, stay, outputAt]
    split
    · next h => subst i; rw [side_natAbs _ _ sign,asAtHead]
    · rfl

/-- One physical transition moves both the output and the folded distance counter
one cell toward the origin. Every other tape remains parked. -/
theorem rewindStep (hne : blank ≠ marker) (neg : Bool) (x : Config A Q I) (n : ℕ) :
    advance M (ret out blank marker neg x (n+1)) =
      some (ret out blank marker neg x n) := by
  have unmarked : (counter blank marker (n+1)).view 0 ≠ marker := by
    simp [counter,Reset.atHead,mark,hne]
    omega
  unfold advance ret rule
  simp only [banks,unmarked, decide_false, Bool.false_eq_true, ↓reduceIte,
    Option.map_some,Option.some.injEq]
  simp only [Config.mk.injEq, true_and]
  funext i
  cases i with
  | none =>
    change (counter blank marker (n+1)).apply ((counter blank marker (n+1)).view 0,.left) = _
    unfold counter
    rw [readMove]
    simp [banks,Move.shift]
  | some i =>
    by_cases h : i = out
    · subst i
      simp only [banks, outputAt, ↓reduceIte, readMove, side_step]
    · simp [banks, outputAt, h, stay]

/-- At distance zero the final transition erases the sentinel. -/
theorem finishStep (neg : Bool) (x : Config A Q I) :
    advance M (ret out blank marker neg x 0) = some (final out blank x) := by
  have atMarker : (counter blank marker 0).view 0 = marker := by
    simp [counter,Reset.atHead,mark]
  unfold advance rule ret
  simp only [banks,atMarker,decide_true, ↓reduceIte, Option.map_some,Option.some.injEq]
  simp only [final, Config.mk.injEq, true_and]
  funext i
  cases i with
  | none =>
    change (counter blank marker 0).apply (blank,.stay) = Tape.loaded blank []
    unfold counter
    rw [Reset.atHead_apply]
    simp only [Nat.cast_zero,Move.shift,add_zero,Reset.atHead,Tape.loaded,Tape.mk.injEq,true_and]
    funext k
    cases k <;> simp [mark,Function.update]
    tauto
  | some i =>
    change (outputAt out x (side neg 0) i).apply ((outputAt out x (side neg 0) i).view 0,.stay) =
      outputAt out x 0 i
    simp [stay, side]

theorem unwind (hne : blank ≠ marker) (neg : Bool) (x : Config A Q I) (n : ℕ) :
    Trace (advance M) (ret out blank marker neg x n) (n+1) (final out blank x) := by
  induction n with
  | zero => exact .single (finishStep out blank marker entry m neg x)
  | succ n ih =>
    simpa only [Nat.add_comm 1 (n+1)] using
      (Trace.cons (rewindStep out blank marker entry m hne neg x n) ih)

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
