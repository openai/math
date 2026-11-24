import OAI.Computability.VPVNP.RAMProcessorSiteTestsWord

/-!
# Finite decision trees on decoded site fields

Each test preserves the site data. The branch pop consumes its temporary
answer. A leaf returns the caller's exit tag on the verdict stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteTests

open TapeWord BurstRAM

variable {w : ℕ}

/-- A site test that compares two word fields, inspects a status flag or checks whether the
choice stream is empty. -/
inductive Atom where
  | compare (op : Comparison.Op) (left right : WordField)
  | flag (f : BitField)
  | emptyChoices

/-- Boolean outcome of a primitive site check on the decoded words, flags and choices of a
snapshot. -/
def Atom.eval (a : Atom) (s : Snapshot w) : Bool :=
  match a with
  | .compare op x y => op.eval (s.words x) (s.words y)
  | .flag f => s.flags f
  | .emptyChoices => s.choices.isEmpty

private def peek (p : Port) (f : Option Bool → Bool) : FiniteRoutine Port :=
  let emit := fun b => Routine.push Port.left (f b)
  let restore := fun b => (Routine.push p b).followedBy (emit (some b))
  .ofRoutine (Routine.popCase p (emit none) (restore false) (restore true))

private theorem peek_run (p : Port) (f : Option Bool → Bool) (s : Stacks Port) (hl : s .left = []) :
    (peek p f).Runs (if (s p).isEmpty then 2 else 3) s (Function.update s .left [f (s p).head?]) := by
  cases he : s p with
  | nil =>
    have hp := Routine.runs_push Port.left (f none) s
    rw [hl] at hp
    apply Routine.runs_popCase_empty p _ _ _ he hp
  | cons b bs =>
    let popped := Function.update s p bs
    have hr : (Routine.push p b).Runs 1 popped s := by
      have h := Routine.runs_push p b popped
      simpa only [popped, Function.update_self, Function.update_idem, ← he, Function.update_eq_self] using h
    have hp := Routine.runs_push Port.left (f (some b)) s
    rw [hl] at hp
    have hb := hr.followedBy hp
    cases b
    · apply Routine.runs_popCase_false p _ _ _ he hb
    · apply Routine.runs_popCase_true p _ _ _ he hb

/-- Stack routine implementing an atomic site test and delivering its Boolean answer on the
left scratch stack. -/
def Atom.machine : Atom → FiniteRoutine Port
  | .compare op x y => SiteTests.compare op x y
  | .flag f => peek (.bit f) (fun b => b.getD false)
  | .emptyChoices => peek .choices Option.isNone

/-- Exact stack-step count for an atomic test. A word comparison costs 20 times the width plus
10, a flag costs three, and testing choices costs two or three according to emptiness. -/
def Atom.ticks (a : Atom) (s : Snapshot w) : ℕ :=
  match a with
  | .compare .. => 20*w+10
  | .flag _ => 3
  | .emptyChoices => if s.choices.isEmpty then 2 else 3

theorem Atom.run (a : Atom) (s : Snapshot w) :
    a.machine.Runs (a.ticks s) s.bank (Function.update s.bank .left [a.eval s]) := by
  cases a with
  | compare op x y => exact compare_runs op x y s
  | flag f => exact peek_run (.bit f) (fun b => b.getD false) s.bank rfl
  | emptyChoices =>
    have h := peek_run .choices Option.isNone s.bank rfl
    cases he : s.choices <;> simpa [Atom.machine, Atom.eval, Atom.ticks, Snapshot.bank, he] using h

/-- Decision to reject execution, finish the current bucket or dispatch another charged call. -/
inductive Exit where
  | reject | finish | dispatch
  deriving DecidableEq

/-- Verdict-stack encoding of the three exits. A leading false bit rejects, and a leading true
bit is followed by false for finish or true for dispatch. -/
def Exit.bits : Exit → List Bool
  | .reject => [false] | .finish => [true, false] | .dispatch => [true, true]

private def leafCode : Exit → FiniteRoutine Port
  | .reject => .ofRoutine (Routine.push Port.verdict false)
  | .finish => .ofRoutine ((Routine.push Port.verdict false).followedBy (Routine.push Port.verdict true))
  | .dispatch => .ofRoutine ((Routine.push Port.verdict true).followedBy (Routine.push Port.verdict true))

private theorem leaf_run (e : Exit) (s : Snapshot w) :
    (leafCode e).Runs e.bits.length s.bank (Function.update s.bank .verdict e.bits) := by
  have two (b : Bool) : ((Routine.push Port.verdict b).followedBy (Routine.push Port.verdict true)).Runs 2
      s.bank (Function.update s.bank .verdict [true, b]) := by
    have h := (Routine.runs_push Port.verdict b s.bank).followedBy
      (Routine.runs_push Port.verdict true (Function.update s.bank .verdict [b]))
    simpa only [Function.update_self, Function.update_idem] using h
  cases e with
  | reject => exact Routine.runs_push _ _ _
  | finish => exact two false
  | dispatch => exact two true

/-- Finite decision tree with primitive site tests at branches and processor exits at leaves. -/
inductive Tree where
  | leaf (e : Exit)
  | branch (a : Atom) (yes no : Tree)

/-- Follow the branch outcomes on a fixed decoded snapshot to obtain the processor exit at the
selected leaf. -/
def Tree.eval : Tree → Snapshot w → Exit
  | .leaf e, _ => e
  | .branch a yes no, s => if a.eval s then yes.eval s else no.eval s

/-- Exact stack-step count along the selected tree path, including each test, its branch pop
and the verdict bits pushed at the leaf. -/
def Tree.ticks : Tree → Snapshot w → ℕ
  | .leaf e, _ => e.bits.length
  | .branch a yes no, s => a.ticks s + ((if a.eval s then yes.ticks s else no.ticks s) + 1)

private def select (yes no : FiniteRoutine Port) : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase Port.left (Routine.halt false) no.body yes.body)

/-- Compile each branch to an atomic test and a pop that selects its successor. At a leaf the
routine pushes the encoded exit onto the verdict stack. -/
def Tree.machine : Tree → FiniteRoutine Port
  | .leaf e => leafCode e
  | .branch a yes no => a.machine.followedBy (select yes.machine no.machine)

/-- A normally returning site test delivers its precise exit code. The
original choices, bounds, status bits and state words remain available. -/
theorem Tree.run (t : Tree) (s : Snapshot w) :
    t.machine.Runs (t.ticks s) s.bank (Function.update s.bank .verdict (t.eval s).bits) := by
  induction t with
  | leaf e => exact leaf_run e s
  | branch a yes no ih₁ ih₂ =>
    have ht := a.run s
    cases h : a.eval s with
    | false =>
      rw [h] at ht
      simp only [Tree.machine, Tree.ticks, Tree.eval, h, Bool.false_eq_true, ite_false]
      apply FiniteRoutine.Runs.followedBy ht
      apply Routine.runs_popCase_false Port.left _ _ _ (tail := []) (Function.update_self ..)
      rw [Function.update_idem, show Function.update s.bank .left [] = s.bank from Function.update_eq_self _ _]
      exact ih₂
    | true =>
      rw [h] at ht
      simp only [Tree.machine, Tree.ticks, Tree.eval, h, ite_true]
      apply FiniteRoutine.Runs.followedBy ht
      apply Routine.runs_popCase_true Port.left _ _ _ (tail := []) (Function.update_self ..)
      rw [Function.update_idem, show Function.update s.bank .left [] = s.bank from Function.update_eq_self _ _]
      exact ih₁

end RAMTape.SiteTests

end VPVNP
end Computability
end OAI
