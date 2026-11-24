import OAI.Computability.VPVNP.RAMTapeUnaryWordValue
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import Mathlib.Tactic.DeriveFintype

/-!
# Fixed stack controls for a physical sorting row counter

The width arrives on a unary stack. Initialization builds a zero word of
that width and restores the width tally. Each advance adds one to the binary
and unary counters. The outgoing carry records when the traversal has reached
the last row, including the one-row case at width zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortOffsets

open BurstRAM UnaryWord TapeWord

/-- Stacks for the unary row width, binary row index, unary row index, temporary bits and
continuation flag. -/
inductive Port | width | index | unary | tmp | again
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control for initializing the binary index from the width, advancing binary and unary row
counts, and recording overflow at the final row. -/
inductive Phase
  | init | zeroBit | saveWidth | restoreWidth | widthMark | start
  | add (carry : Bool) | emit (b carry : Bool)
  | restore (overflow : Bool) | put (b overflow : Bool)
  | next (overflow : Bool) | flag (overflow : Bool)
  | clearIndex | clearUnary | done
  deriving DecidableEq, Fintype

/-- Build a width-sized zero index and execute a carry-propagating row increment while
maintaining its unary copy. -/
def code : StackCode Port Phase
  | .init => .pop .width fun b => b.elim .restoreWidth (fun _ => .zeroBit)
  | .zeroBit => .push .index false .saveWidth
  | .saveWidth => .push .tmp true .init
  | .restoreWidth => .pop .tmp fun b => b.elim .start (fun _ => .widthMark)
  | .widthMark => .push .width true .restoreWidth
  | .start => .push .again true .done
  | .add carry => .pop .index fun b =>
      b.elim (.restore carry) (fun bit => .emit (bit ^^ carry) (bit && carry))
  | .emit b c => .push .tmp b (.add c)
  | .restore ov => .pop .tmp fun b => b.elim (.next ov) (fun bit => .put bit ov)
  | .put b ov => .push .index b (.restore ov)
  | .next ov => .push .unary true (.flag ov)
  | .flag ov => .push .again (!ov) .done
  | .clearIndex => .pop .index fun b => b.elim .clearUnary (fun _ => .clearIndex)
  | .clearUnary => .pop .unary fun b => b.elim .done (fun _ => .clearUnary)
  | .done => .halt true

/-- Install the width, binary index, unary index, scratch and continuation bit lists on the
row-counter ports. -/
def store (w x u tmp again : List Bool) : Stacks Port
  | .width => w
  | .index => x
  | .unary => u
  | .tmp => tmp
  | .again => again

private theorem set_store (w x u t f v : List Bool) (k : Port) :
    Function.update (store w x u t f) k v = match k with
      | .width => store v x u t f
      | .index => store w v u t f
      | .unary => store w x v t f
      | .tmp => store w x u v f
      | .again => store w x u t v := by
  funext j; cases k <;> cases j <;> simp [store]

local macro "offset_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, set_store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none])

/-- Unary encoding of a natural number as that many true bits. -/
abbrev ones (n : ℕ) := List.replicate n true
private abbrev zeros (n : ℕ) := List.replicate n false

private theorem alloc_run (n : ℕ) (x t : List Bool) :
    StackRuns code (3*n+1) .init (store (ones n) x [] t [])
      .restoreWidth (store [] (zeros n ++ x) [] (ones n ++ t) []) := by
  induction n generalizing x t with
  | zero => offset_step; exact .nil ..
  | succ n ih =>
    simp only [Nat.mul_succ]
    change StackRuns code _ _ (store (true :: ones n) x [] t []) _ _
    offset_step; offset_step; offset_step
    simpa only [zeros, ones, List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (false :: x) (true :: t)

private theorem width_run (n : ℕ) (w x : List Bool) :
    StackRuns code (2*n+2) .restoreWidth (store w x [] (ones n) []) .done
      (store (ones n ++ w) x [] [] [true]) := by
  induction n generalizing w with
  | zero => offset_step; offset_step; exact .nil ..
  | succ n ih =>
    rw [show 2*(n+1)+2 = (2*n+2)+1+1 by omega]
    change StackRuns code _ _ (store w x [] (true :: ones n) []) _ _
    rw [show ones (n+1) ++ w = ones n ++ true :: w by
      simp [ones, List.replicate_succ', List.append_assoc]]
    offset_step; offset_step
    exact ih (true :: w)

/-- Initialize from the supplied width. -/
theorem initialize_run (h : ℕ) :
    StackRuns code (5*h+3) .init (store (ones h) [] [] [] []) .done
      (store (ones h) (wordBits (0 : Word h)) [] [] [true]) := by
  have h₁ := alloc_run h [] []
  have h₂ := width_run h [] (zeros h)
  simp only [List.append_nil] at h₁ h₂
  simpa only [zeros_wordBits, show 3*h+1+(2*h+2) = 5*h+3 by omega] using h₁.trans h₂

private theorem scan_run (carry : Bool) (w x u t : List Bool) :
    StackRuns code (2*x.length+1) (.add carry) (store w x u t [])
      (.restore (incScan carry x).2) (store w [] u ((incScan carry x).1.reverse ++ t) []) := by
  induction x generalizing carry t with
  | nil => offset_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, incScan, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    offset_step; offset_step
    exact ih (b && carry) ((b ^^ carry) :: t)

private theorem restore_run (ov : Bool) (w x u t : List Bool) :
    StackRuns code (2*t.length+3) (.restore ov) (store w x u t []) .done
      (store w (t.reverse ++ x) (true :: u) [] [!ov]) := by
  induction t generalizing x with
  | nil => offset_step; offset_step; offset_step; exact .nil ..
  | cons b t ih =>
    rw [show 2*(b::t).length+3 = (2*t.length+3)+1+1 by simp [Nat.mul_succ]]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    offset_step; offset_step
    exact ih (b :: x)

/-- Advance both counters and set the continuation flag from the binary carry out. -/
theorem advance_run (w x u : List Bool) :
    StackRuns code (4*x.length+4) (.add true) (store w x u [] []) .done
      (store w (incScan true x).1 (true :: u) [] [!(incScan true x).2]) := by
  have h₁ := scan_run true w x u []
  have h₂ := restore_run (incScan true x).2 w [] u (incScan true x).1.reverse
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse, incScan_length] at h₁ h₂
  simpa only [show 2*x.length+1+(2*x.length+3) = 4*x.length+4 by omega] using h₁.trans h₂

private theorem clear_unary (w u : List Bool) :
    StackRuns code (u.length+1) .clearUnary (store w [] u [] []) .done (store w [] [] [] []) := by
  induction u with
  | nil => offset_step; exact .nil ..
  | cons b u ih => offset_step; exact ih

/-- Clear both counters after the final row. -/
theorem clear_run (w x u : List Bool) :
    StackRuns code (x.length+u.length+2) .clearIndex (store w x u [] []) .done (store w [] [] [] []) := by
  induction x with
  | nil => offset_step; simpa using clear_unary w u
  | cons b x ih =>
    rw [show (b::x).length+u.length+2 = (x.length+u.length+2)+1 by simp; omega]
    offset_step
    exact ih

end RAMTape.SortOffsets

end VPVNP
end Computability
end OAI
