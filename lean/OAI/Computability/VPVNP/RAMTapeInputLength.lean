import OAI.Computability.VPVNP.RAMTapeInputPorts

/-!
# Reading the complete input length before parsing the site fields

The size stack acquires one unary mark per input bit, including program-prefix
bits and padding. The control saves each popped bit on a temporary stack and
then transfers the bits back, restoring the original input in head-first order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- States of the length pass that saves every input bit, counts it with a unary mark, and
restores the input. -/
inductive LengthPhase where
  | scan
  | save (bit : Bool)
  | mark
  | restore
  | put (bit : Bool)
  | done
  deriving DecidableEq, Fintype

/-- A fixed control, independent of the length and contents of the physical input. -/
def lengthCode : StackCode InputPort LengthPhase
  | .scan => .pop .input (fun b ↦ b.elim .restore .save)
  | .save b => .push .tmp b .mark
  | .mark => .push .size true .scan
  | .restore => .pop .tmp (fun b ↦ b.elim .done .put)
  | .put b => .push .input b .restore
  | .done => .halt true

private def lengthStore (base : Stacks InputPort) (input tmp size : List Bool) : Stacks InputPort
  | .input => input
  | .tmp => tmp
  | .size => size
  | k => base k

private theorem write_input (s : Stacks InputPort) (x t n v : List Bool) :
    Function.update (lengthStore s x t n) .input v = lengthStore s v t n := by
  funext k
  cases k <;> simp [lengthStore, Function.update]

private theorem write_tmp (s : Stacks InputPort) (x t n v : List Bool) :
    Function.update (lengthStore s x t n) .tmp v = lengthStore s x v n := by
  funext k
  cases k <;> simp [lengthStore, Function.update]

private theorem write_size (s : Stacks InputPort) (x t n v : List Bool) :
    Function.update (lengthStore s x t n) .size v = lengthStore s x t v := by
  funext k
  cases k <;> simp [lengthStore, Function.update]

local macro "length_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [write_input, write_tmp, write_size, lengthStore, List.head?_cons, List.tail_cons,
    List.head?_nil, List.tail_nil, Option.elim_some, Option.elim_none])

private theorem scan_length (s : Stacks InputPort) (x t n : List Bool) :
    StackRuns lengthCode (3 * x.length + 1) .scan (lengthStore s x t n) .restore
      (lengthStore s [] (x.reverse ++ t) (List.replicate x.length true ++ n)) := by
  induction x generalizing t n with
  | nil => length_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.replicate_succ']
    length_step
    length_step
    length_step
    exact ih (b :: t) (true :: n)

private theorem restore_input (s : Stacks InputPort) (x t n : List Bool) :
    StackRuns lengthCode (2 * t.length + 1) .restore (lengthStore s x t n) .done
      (lengthStore s (t.reverse ++ x) [] n) := by
  induction t generalizing x with
  | nil => length_step; exact .nil ..
  | cons b t ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    length_step
    length_step
    exact ih (b :: x)

/-- Exactly five stack instructions per input bit and two end tests. With an
empty size stack the output is the unary input length. Every other stack,
including the complete input, agrees with its value on entry. -/
theorem length_runs (s : Stacks InputPort) (ht : s .tmp = []) :
    StackRuns lengthCode (5 * (s .input).length + 2) .scan s .done
      (Function.update s .size (List.replicate (s .input).length true ++ s .size)) := by
  let x := s .input
  let n := List.replicate x.length true ++ s .size
  have hscan := scan_length s x [] (s .size)
  have hrestore := restore_input s [] x.reverse n
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hscan hrestore
  have hstart : lengthStore s x [] (s .size) = s := by
    funext k
    cases k <;> simp [lengthStore, x, ht]
  have hdone : lengthStore s x [] n = Function.update s .size n := by
    funext k
    cases k <;> simp [lengthStore, Function.update, x, ht]
  have h := hscan.trans hrestore
  rw [hstart, hdone, show 3 * x.length + 1 + (2 * x.length + 1) = 5 * x.length + 2 by omega] at h
  exact h

end RAMTape

end VPVNP
end Computability
end OAI
