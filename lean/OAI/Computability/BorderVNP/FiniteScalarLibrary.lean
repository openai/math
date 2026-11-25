import OAI.Computability.BorderVNP.FiniteScalarRoundCell

/-! # A common native library for the signed cell and its field output

The ordinary cell interpreter and the finite-field scalar scanner both use
blank/zero/one symbols. Their controls embed disjointly in one finite state
type. The scalar routine scans one of the cell interpreter's tapes and leaves
every other tape stationary, preserving its bounded running time and original
choice strings.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarLibrary

open TeamPrivateTape TeamPrivateValue TeamSite VPVNP.BurstRAM
open scoped Classical

variable {Q R Γ : Type} {m g : ℕ} {F : Type*} [Field F] [Fintype F]

private def changeControl (f : Q → R) (c : TapeCommand Q Γ m) : TapeCommand R Γ m :=
  ⟨f c.next,c.write,c.direction⟩

private theorem changed_next (f : Q → R) (c : TapeCommand Q Γ m) : (changeControl f c).next = f c.next := rfl

private theorem changed_apply (f : Q → R) (c : TapeCommand Q Γ m) (blank : Γ) (ts : Fin m → SymbolTape Γ) :
    (changeControl f c).apply blank ts = c.apply blank ts := rfl

private def changeChoice (f : Q → R) : TapeChoice Q Γ m → TapeChoice R Γ m
  | .halt a b => .halt a b
  | .one c => .one (changeControl f c)
  | .two l r => .two (changeControl f l) (changeControl f r)

/-- Install the original native cell table on the left summand. -/
def leftTable (P : TapeTable Q Γ m) : TapeTable (Q ⊕ R) Γ m
  | .inl q, x => changeChoice Sum.inl (P q x)
  | .inr _, _ => .halt false false

/-- The original private routine uses the same symbols, input, head arrangement,
and signed halt convention on the common control. -/
def leftMacro (M : Macro Q Γ m g) : Macro (Q ⊕ R) Γ m g :=
  ⟨M.alphabet,M.digit,M.inputTape,leftTable M.table,.inl M.start⟩

/-- Include an original field-return convention on the corresponding control summand. -/
def leftReturn (w : FieldSelect.Return Q Γ F m) : FieldSelect.Return (Q ⊕ R) Γ F m
  | .inl q, x, b => w q x b
  | .inr _, _, _ => 0

omit [Fintype F] in
/-- All original field-returning paths survive the embedding with identical
terminal outputs, cutoff and private bits. -/
theorem left_value (P : TapeTable Q Γ m) (blank : Γ) (w : FieldSelect.Return Q Γ F m)
    (f : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) (bs : List Bool) :
    FieldSelect.nativeReturn (leftTable (R := R) P) blank (leftReturn w) f (.inl q) ts bs =
      FieldSelect.nativeReturn P blank w f q ts bs := by
  induction f generalizing q ts bs with
  | zero => rfl
  | succ f ih =>
    cases h : P q (fun i => (ts i).head) with
    | halt a b => simp [FieldSelect.nativeReturn,leftTable,changeChoice,leftReturn,h]
    | one c => simpa only [FieldSelect.nativeReturn,leftTable,changeChoice,h,changed_next,changed_apply] using ih c.next (c.apply blank ts) bs
    | two l r => cases bs with
      | nil => simp [FieldSelect.nativeReturn,leftTable,changeChoice,h]
      | cons b bs => cases b <;> simp [FieldSelect.nativeReturn,leftTable,changeChoice,h,changed_next,changed_apply,ih]

/-- The unchanged signed cell routine satisfies exactly the same native bound. -/
theorem left_bounded (P : TapeTable Q Γ m) (blank : Γ) (f : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) :
    TapeStops (leftTable (R := R) P) blank f (.inl q) ts ↔ TapeStops P blank f q ts := by
  induction f generalizing q ts with
  | zero => rfl
  | succ f ih =>
    cases h : P q (fun i => (ts i).head) <;> simp only [TapeStops,leftTable,changeChoice,h,changed_next,changed_apply,ih]

private def trackControl (f : Q → R) (c : Command Q m) : Command R m := ⟨f c.next,c.write,c.direction⟩

private theorem track_left (a : Alphabet Γ g) (P : TapeTable Q Γ m) (q : Q) (bs : Fin (m*g) → Bool) :
    trackTable a (leftTable (R := R) P) (.inl q) bs =
      match trackTable a P q bs with
      | .halt x y => .halt x y
      | .one c => .one (trackControl Sum.inl c)
      | .two l r => .two (trackControl Sum.inl l) (trackControl Sum.inl r) := by
  simp only [trackTable,leftTable]
  cases P q (fun i => a.read (fun j => bs (finProdFinEquiv (i,j)))) <;> rfl

private theorem left_eval (M : Macro Q Γ m g) (f : ℕ) (q : Q) (ts : Fin (m*g) → Track) (bs : List Bool) :
    TeamPrivateCall.evaluate (trackTable M.alphabet (leftTable (R := R) M.table)) f (.inl q) ts bs =
      TeamPrivateCall.evaluate (trackTable M.alphabet M.table) f q ts bs := by
  induction f generalizing q ts bs with
  | zero => rfl
  | succ f ih =>
    rw [TeamPrivateCall.evaluate,TeamPrivateCall.evaluate,track_left]
    cases op : trackTable M.alphabet M.table q (heads ts) with
    | halt x y => rfl
    | one c => exact ih c.next (c.apply ts) bs
    | two l r => cases bs with
      | nil => rfl
      | cons b bs => cases b <;> apply ih

/-- The originally issued signed RAM call returns its same sign, including zero
and invalid or timed-out arguments, after embedding in the combined library. -/
theorem left_eval_eq {w : ℕ} (M : Macro Q Γ m g) (f : ℕ) (vs : List (Word w)) (bs : List Bool) :
    (leftMacro (R := R) M).eval f vs bs = M.eval f vs bs := by
  unfold Macro.eval
  exact congrArg (Option.map _) (left_eval (R := R) M f M.start (M.initial vs) bs)

/-- Widen a command of the one-tape field routine to the fixed caller
architecture. The other scanned symbols and head positions are preserved. -/
def rightCommand (tape : Fin m) (sym : Fin m → Γ) (c : TapeCommand R Γ 1) : TapeCommand (Q ⊕ R) Γ m :=
  ⟨.inr c.next,Function.update sym tape (c.write 0),fun i => if i=tape then c.direction 0 else none⟩

private theorem right_next (tape : Fin m) (sym : Fin m → Γ) (c : TapeCommand R Γ 1) :
    (rightCommand (Q := Q) tape sym c).next = Sum.inr c.next := rfl

/-- Use one designated tape for all native field-input symbols. -/
def rightTable (tape : Fin m) (P : TapeTable R Γ 1) : TapeTable (Q ⊕ R) Γ m
  | .inl _, _ => .halt false false
  | .inr q, sym => match P q (fun _ => sym tape) with
    | .halt a b => .halt a b
    | .one c => .one (rightCommand tape sym c)
    | .two l r => .two (rightCommand tape sym l) (rightCommand tape sym r)

/-- Recover the scalar return from the one active symbol tape and right control. -/
def rightReturn (tape : Fin m) (out : FieldSelect.Return R Γ F 1) : FieldSelect.Return (Q ⊕ R) Γ F m
  | .inr q, sym, b => out q (fun _ => sym tape) b
  | .inl _, _, _ => 0

private theorem active_move (tape : Fin m) (blank : Γ) (ts : Fin m → SymbolTape Γ) (c : TapeCommand R Γ 1) :
    (fun _ : Fin 1 => ((rightCommand (Q := Q) tape (fun i => (ts i).head) c).apply blank ts) tape) =
      c.apply blank (fun _ => ts tape) := by
  funext i
  have hi : i=0 := Subsingleton.elim ..
  simp [rightCommand,TapeCommand.apply,hi]

omit [Fintype F] in
/-- Widening the scalar routine preserves its field result on all choice strings. -/
theorem right_value (tape : Fin m) (P : TapeTable R Γ 1) (blank : Γ) (out : FieldSelect.Return R Γ F 1)
    (fuel : ℕ) (q : R) (ts : Fin m → SymbolTape Γ) (choices : List Bool) :
    FieldSelect.nativeReturn (rightTable (Q := Q) tape P) blank (rightReturn tape out) fuel (.inr q) ts choices =
      FieldSelect.nativeReturn P blank out fuel q (fun _ => ts tape) choices := by
  induction fuel generalizing q ts choices with
  | zero => rfl
  | succ f ih =>
    cases op : P q (fun _ => (ts tape).head) with
    | halt a b => simp [FieldSelect.nativeReturn,rightTable,rightReturn,op]
    | one c => simp only [FieldSelect.nativeReturn,rightTable,op,right_next,ih,active_move]
    | two l r =>
      cases choices with
      | nil => simp [FieldSelect.nativeReturn,rightTable,op]
      | cons b bs => cases b <;> simp only [FieldSelect.nativeReturn,rightTable,op,Bool.false_eq_true,
          ite_false,ite_true,right_next,ih,active_move]

/-- All branches of the widened routine still halt at the same native cutoff. -/
theorem right_bounded (tape : Fin m) (P : TapeTable R Γ 1) (blank : Γ) (f : ℕ) (q : R) (ts : Fin m → SymbolTape Γ) :
    TapeStops (rightTable (Q := Q) tape P) blank f (.inr q) ts ↔ TapeStops P blank f q (fun _ => ts tape) := by
  induction f generalizing q ts with
  | zero => rfl
  | succ f ih =>
    cases op : P q (fun _ => (ts tape).head) <;> simp only [TapeStops,rightTable,op,right_next,ih,active_move]

end FiniteScalarLibrary

end BorderVNP
end Computability
end OAI
