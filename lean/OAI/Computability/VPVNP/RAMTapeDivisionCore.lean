import OAI.Computability.VPVNP.RAMTapeWordDivision
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Fixed stack control for restoring division

The control reverses the dividend to expose its most significant bit, tests
the divisor for zero, and initializes a zero remainder of the same width. A
forward scan saves the divisor, candidate bits and trial difference on three
scratch stacks. The restore scan puts the divisor back and uses the final
borrow to choose the new remainder.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.DivisionStack

open RAMTape

/-- Ports for the dividend, its reversed feed, divisor, quotient, remainder, and three
trial-subtraction stacks. -/
inductive Port where
  | input | feed | divisor | remainder | quotient | saved | original | difference
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control of restoring division, including dividend reversal, zero-divisor handling, trial
subtraction, and quotient-bit emission. -/
inductive State where
  | reverseInput | saveInput (b : Bool)
  | init (nonzero : Bool) | saveInit (d nonzero : Bool) | initZero (nonzero : Bool)
  | restoreInit (nonzero : Bool) | putInit (d nonzero : Bool)
  | clearRemainder | zeroLoop | zeroQuot (b : Bool) | zeroRem (b : Bool)
  | outer
  | forward (borrow prev : Bool) | readR (borrow prev d : Bool)
  | saveD (d orig result borrow prev : Bool) | saveOrig (orig result borrow prev : Bool)
  | saveDiff (result borrow prev : Bool)
  | restore (borrow : Bool) | putD (d borrow : Bool)
  | readOrig (borrow : Bool) | readDiff (orig borrow : Bool)
  | putR (b borrow : Bool) | digit (borrow : Bool)
  | done | reject
  deriving DecidableEq, Fintype

/-- Perform binary restoring division from the most significant dividend bit. For a zero
divisor emit a zero quotient and return the dividend as the remainder. -/
def code : StackCode Port State
  | .reverseInput => .pop .input (fun | none => .init false | some b => .saveInput b)
  | .saveInput b => .push .feed b .reverseInput
  | .init nonzero => .pop .divisor
      (fun | none => .restoreInit nonzero | some d => .saveInit d (nonzero || d))
  | .saveInit d nonzero => .push .saved d (.initZero nonzero)
  | .initZero nonzero => .push .remainder false (.init nonzero)
  | .restoreInit nonzero => .pop .saved
      (fun | none => if nonzero then .outer else .clearRemainder | some d => .putInit d nonzero)
  | .putInit d nonzero => .push .divisor d (.restoreInit nonzero)
  | .clearRemainder => .pop .remainder (fun | none => .zeroLoop | some _ => .clearRemainder)
  | .zeroLoop => .pop .feed (fun | none => .done | some b => .zeroQuot b)
  | .zeroQuot b => .push .quotient false (.zeroRem b)
  | .zeroRem b => .push .remainder b .zeroLoop
  | .outer => .pop .feed (fun | none => .done | some b => .forward false b)
  | .forward borrow prev => .pop .divisor
      (fun | none => .restore (subBit borrow prev false).2 | some d => .readR borrow prev d)
  | .readR borrow prev d => .pop .remainder (fun
      | none => .reject
      | some r =>
        let t := subBit borrow prev d
        .saveD d prev t.1 t.2 r)
  | .saveD d orig result borrow prev => .push .saved d (.saveOrig orig result borrow prev)
  | .saveOrig orig result borrow prev => .push .original orig (.saveDiff result borrow prev)
  | .saveDiff result borrow prev => .push .difference result (.forward borrow prev)
  | .restore borrow => .pop .saved (fun | none => .digit borrow | some d => .putD d borrow)
  | .putD d borrow => .push .divisor d (.readOrig borrow)
  | .readOrig borrow => .pop .original (fun | none => .reject | some b => .readDiff b borrow)
  | .readDiff orig borrow => .pop .difference (fun
      | none => .reject
      | some diff => .putR (if borrow then orig else diff) borrow)
  | .putR b borrow => .push .remainder b (.restore borrow)
  | .digit borrow => .push .quotient (!borrow) .outer
  | .done => .halt true
  | .reject => .halt false

/-- Bit stacks for restoring division, including the trial remainder and difference used to
resolve each quotient digit. -/
structure Data where
  /-- Dividend bits before reversal into most-significant-first order. -/
  input : List Bool
  /-- Remaining dividend bits in the order in which division consumes them. -/
  feed : List Bool
  /-- Divisor word restored after every trial subtraction. -/
  divisor : List Bool
  /-- Current partial remainder of the division. -/
  remainder : List Bool
  /-- Quotient digits accumulated as the dividend bits are consumed. -/
  quotient : List Bool
  /-- Divisor bits held temporarily during initialization or trial subtraction. -/
  saved : List Bool
  /-- Candidate remainder bits saved before subtraction for the borrow case. -/
  original : List Bool
  /-- Trial-difference bits saved for the case in which subtraction succeeds. -/
  difference : List Bool

/-- Read the division bank by its stack port. -/
def Data.stacks (s : Data) : Stacks Port
  | .input => s.input
  | .feed => s.feed
  | .divisor => s.divisor
  | .remainder => s.remainder
  | .quotient => s.quotient
  | .saved => s.saved
  | .original => s.original
  | .difference => s.difference

/-- Replace one of the eight division stacks. -/
def Data.set (s : Data) : Port → List Bool → Data
  | .input, x => {s with input := x}
  | .feed, x => {s with feed := x}
  | .divisor, x => {s with divisor := x}
  | .remainder, x => {s with remainder := x}
  | .quotient, x => {s with quotient := x}
  | .saved, x => {s with saved := x}
  | .original, x => {s with original := x}
  | .difference, x => {s with difference := x}

theorem Data.set_stacks (s : Data) (i : Port) (xs : List Bool) :
    (s.set i xs).stacks = Function.update s.stacks i xs := by
  funext j
  cases i <;> cases j <;> rfl

/-- One deterministic transition, written using concrete record projections
to simplify the verified word-level macros. -/
def tick (q : State) (s : Data) : Option (State × Data) :=
  match code q with
  | .pop k f => some (f (s.stacks k).head?, s.set k (s.stacks k).tail)
  | .push k b next => some (next, s.set k (b :: s.stacks k))
  | .goto next => some (next, s)
  | .choose _ _ | .halt _ => none

/-- An execution of the division control between two states and banks in exactly the given
number of stack steps. -/
abbrev Run (n : ℕ) (q : State) (s : Data) (q' : State) (t : Data) :=
  StackRuns code n q s.stacks q' t.stacks

theorem stepOfTick {q q' : State} {s t : Data} (h : tick q s = some (q', t)) :
    StackStep code q s.stacks q' t.stacks := by
  unfold tick at h
  cases hc : code q with
  | push k b next =>
    rw [hc] at h
    cases h
    rw [Data.set_stacks]
    exact .push hc
  | pop k f =>
    rw [hc] at h
    cases h
    rw [Data.set_stacks]
    exact .pop hc
  | goto next => rw [hc] at h; cases h; exact .goto hc
  | choose | halt => simp [hc] at h

theorem prepend {q q' t : State} {s s' u : Data} {n : ℕ}
    (h : tick q s = some (q', s')) (tail : Run n q' s' t u) : Run (n + 1) q s t u :=
  .cons (stepOfTick h) tail

end TapeWord.DivisionStack

end VPVNP
end Computability
end OAI
