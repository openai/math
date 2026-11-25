import OAI.Computability.BorderVNP.CellStackTape

/-! # Reading binary integers from sparse private descriptors

A field is self-delimiting and most-significant digit first. The two stack sweeps double the
current unary magnitude, then add the new digit. Unary scan offsets occur only on the private
tapes. The routine retains the unconsumed descriptor suffix verbatim.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.FieldDecoder

open VPVNP.RAMTape

/-- Self-delimiting binary digits; a zero tag ends the field. -/
def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

/-- Accumulated magnitude while reading a big-endian field. -/
def magnitude : ℕ → List Bool → ℕ
  | a, [] => a
  | a, b :: bs => magnitude (2*a + b.toNat) bs

/-- Data stack, running unary integer, and doubling scratch. -/
inductive Port where
  | input | count | scratch
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Private parser labels. No input-dependent natural number is carried in the control. -/
inductive Phase where
  | tag | digit | double (b : Bool) | first (b : Bool) | second (b : Bool)
  | restore (b : Bool) | put (b : Bool) | low (b : Bool) | done | reject
  deriving DecidableEq, Fintype

/-- Complete finite stack table of the field reader. -/
def code : StackCode Port Phase
  | .tag => .pop .input fun b => b.elim .reject fun present => if present then .digit else .done
  | .digit => .pop .input fun b => b.elim .reject Phase.double
  | .double b => .pop .count fun v => if v.isSome then .first b else .restore b
  | .first b => .push .scratch true (.second b)
  | .second b => .push .scratch true (.double b)
  | .restore b => .pop .scratch fun v => if v.isSome then .put b else .low b
  | .put b => .push .count true (.restore b)
  | .low b => if b then .push .count true .tag else .goto .tag
  | .done => .halt true
  | .reject => .halt false

/-- Bank at a sweep boundary, with both integer stacks in unary. -/
def bank (bits : List Bool) (count scratch : ℕ) : Stacks Port
  | .input => bits
  | .count => List.replicate count true
  | .scratch => List.replicate scratch true

private theorem pop_input (bits bits' : List Bool) (a s : ℕ) :
    Function.update (bank bits a s) .input bits' = bank bits' a s := by
  funext k; cases k <;> simp [bank]

private theorem pop_count (bits : List Bool) (a s a' : ℕ) :
    Function.update (bank bits a s) .count (List.replicate a' true) = bank bits a' s := by
  funext k; cases k <;> simp [bank]

private theorem pop_scratch (bits : List Bool) (a s s' : ℕ) :
    Function.update (bank bits a s) .scratch (List.replicate s' true) = bank bits a s' := by
  funext k; cases k <;> simp [bank]

private theorem push_count (bits : List Bool) (a s : ℕ) :
    Function.update (bank bits a s) .count (true :: List.replicate a true) = bank bits (a+1) s := by
  funext k; cases k <;> simp [bank, List.replicate_succ]

private theorem push_scratch (bits : List Bool) (a s : ℕ) :
    Function.update (bank bits a s) .scratch (true :: List.replicate s true) = bank bits a (s+1) := by
  funext k; cases k <;> simp [bank, List.replicate_succ]

local macro "decoder_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_
         | refine StackRuns.cons (.goto rfl) ?_)
  <;> try simp only [bank, List.head?_cons, List.tail_cons, List.tail_replicate, pop_count, pop_scratch,
    push_count, push_scratch, pop_input, List.head?_nil, Option.elim_some, Option.elim_none,
    List.head?_replicate, Nat.succ_ne_zero, dite_false, ite_true, ite_false, ↓reduceIte,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, Nat.add_one_sub_one])

private theorem double_run (bits : List Bool) (b : Bool) (a s : ℕ) :
    StackRuns code (3*a+1) (.double b) (bank bits a s)
      (.restore b) (bank bits 0 (2*a+s)) := by
  induction a generalizing s with
  | zero =>
    simp only [mul_zero, zero_add]
    decoder_step
    exact .nil ..
  | succ a ih =>
    rw [Nat.mul_succ, show 3*a+3+1 = (3*a+1)+1+1+1 by omega, Nat.mul_succ]
    decoder_step
    decoder_step
    decoder_step
    rw [show 2*a+2+s = 2*a+(s+1+1) by omega]; exact ih _

private theorem restore_run (bits : List Bool) (b : Bool) (a s : ℕ) :
    StackRuns code (2*s+1) (.restore b) (bank bits a s) (.low b) (bank bits (s+a) 0) := by
  induction s generalizing a with
  | zero =>
    simp only [mul_zero, zero_add]
    decoder_step
    exact .nil ..
  | succ s ih =>
    rw [Nat.mul_succ, show 2*s+2+1 = (2*s+1)+1+1 by omega]
    decoder_step
    decoder_step
    rw [show s+1+a = s+(a+1) by omega]; exact ih _

/-- Exact number of elementary steps for all the binary digits and the terminator. -/
def steps : ℕ → List Bool → ℕ
  | _, [] => 1
  | a, b :: bs => 7*a + 5 + steps (2*a + b.toNat) bs

/-- The finite-control parser expands the compact binary field privately and preserves
the following fields, including for a zero-length digit string and leading zeroes. -/
theorem run (bs suffix : List Bool) (a : ℕ) :
    StackRuns code (steps a bs) .tag (bank (frame bs ++ suffix) a 0) .done
      (bank suffix (magnitude a bs) 0) := by
  induction bs generalizing a with
  | nil =>
    simp only [frame, steps, magnitude, List.cons_append, List.nil_append]
    decoder_step
    exact .nil ..
  | cons b bs ih =>
    let s := frame bs ++ suffix
    have d := double_run s b a 0
    rw [Nat.add_zero] at d
    have r := restore_run s b 0 (2*a)
    rw [Nat.add_zero] at r
    have lo : StackRuns code 1 (.low b) (bank s (2*a) 0) .tag (bank s (2*a+b.toNat) 0) := by
      cases b <;> decoder_step <;> exact .nil ..
    have next := (((d.trans r).trans lo).trans (ih (2*a+b.toNat)))
    rw [steps, show 7*a+5+steps (2*a+b.toNat) bs =
      ((3*a+1 + (2*(2*a)+1) + 1) + steps (2*a+b.toNat) bs)+1+1 by omega]
    simp only [frame, List.cons_append, magnitude]
    decoder_step
    decoder_step
    exact next

private theorem magnitude_ge (a : ℕ) (bs : List Bool) : a ≤ magnitude a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => exact le_trans (by omega : a ≤ 2*a+b.toNat) (ih _)

/-- The tape cost is linear in the number of digits times the magnitude actually used.
This permits small local offsets to be supplied in a common padded word format. -/
theorem steps_le (a : ℕ) (bs : List Bool) :
    steps a bs ≤ (7*magnitude a bs+5)*bs.length+1 := by
  induction bs generalizing a with
  | nil => simp [steps, magnitude]
  | cons b bs ih =>
    have hg := magnitude_ge (2*a+b.toNat) bs
    have hr := ih (2*a+b.toNat)
    simp only [steps, magnitude, List.length_cons, Nat.mul_succ]
    omega

end CellMacro.FieldDecoder

end BorderVNP
end Computability
end OAI
