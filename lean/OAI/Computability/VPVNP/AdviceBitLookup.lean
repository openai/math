import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Reading a bit at a unary address in circuit advice

The instruction stream starts with one `true` per skipped value and a terminating
`false`. The routine saves the skipped prefix, copies the addressed bit to the
result stack, and restores the valuation stack in its original order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AdviceBitLookup

/-- The four stacks used to consume a unary address, inspect the valuation, save its skipped
prefix, and return the selected bit. -/
inductive Port where
  | stream | values | scratch | result
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.stream, .values, .scratch, .result}, fun p => by cases p <;> simp⟩

/-- Finite control for skipping valuation bits, reading the addressed bit, and restoring the
skipped prefix in its original order. -/
inductive State where
  | index | skip | save (b : Bool) | read | replace (b : Bool) | write (b : Bool)
  | restore | put (b : Bool) | done | reject
  deriving DecidableEq, Fintype

/-- Fixed finite control. A missing delimiter or an out-of-bounds address rejects. -/
def code : StackCode Port State
  | .index => .pop .stream fun b => b.elim .reject fun v => if v then .skip else .read
  | .skip => .pop .values fun b => b.elim .reject .save
  | .save b => .push .scratch b .index
  | .read => .pop .values fun b => b.elim .reject .replace
  | .replace b => .push .values b (.write b)
  | .write b => .push .result b .restore
  | .restore => .pop .scratch fun b => b.elim .done .put
  | .put b => .push .values b .restore
  | .done => .halt true
  | .reject => .halt false

/-- Assign the supplied instruction stream, valuation, saved prefix, and output to their
respective lookup stacks. -/
def store (stream values scratch result : List Bool) : Stacks Port
  | .stream => stream
  | .values => values
  | .scratch => scratch
  | .result => result

private theorem update_store (a v s r xs : List Bool) (p : Port) :
    Function.update (store a v s r) p xs = match p with
      | .stream => store xs v s r
      | .values => store a xs s r
      | .scratch => store a v xs r
      | .result => store a v s xs := by
  funext q
  cases p <;> cases q <;> simp [store, Function.update]

local macro "lookup_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [update_store, store, List.head?_cons, List.tail_cons,
    List.head?_nil, List.tail_nil, Option.elim_some, Option.elim_none, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true])

private theorem scan (pre : List Bool) (bit : Bool) (rest stream saved result : List Bool) :
    StackRuns code (3 * pre.length + 4) .index
      (store (List.replicate pre.length true ++ false :: stream) (pre ++ bit :: rest) saved result)
      .restore (store stream (bit :: rest) (pre.reverse ++ saved) (bit :: result)) := by
  induction pre generalizing saved with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.replicate_zero, List.nil_append,
      List.reverse_nil]
    lookup_step; lookup_step; lookup_step; lookup_step
    exact .nil ..
  | cons a pre ih =>
    simp only [List.length_cons, Nat.mul_succ, List.replicate_succ, List.cons_append,
      List.reverse_cons, List.append_assoc]
    lookup_step; lookup_step; lookup_step
    exact ih (a :: saved)

private theorem restore (stream values saved result : List Bool) :
    StackRuns code (2 * saved.length + 1) .restore (store stream values saved result)
      .done (store stream (saved.reverse ++ values) [] result) := by
  induction saved generalizing values with
  | nil =>
    lookup_step
    exact .nil ..
  | cons a saved ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    lookup_step; lookup_step
    exact ih (a :: values)

/-- A lookup takes exactly five instructions per skipped bit and five fixed
instructions. Both the remaining advice and the old result tail are preserved. -/
theorem lookup_runs (values streamTail resultTail : List Bool) (k : ℕ) (hk : k < values.length) :
    StackRuns code (5 * k + 5) .index
      (store (List.replicate k true ++ false :: streamTail) values [] resultTail)
      .done (store streamTail values [] (values[k] :: resultTail)) := by
  have length_pre : (values.take k).length = k := by simp [hk.le]
  have split : values.take k ++ values[k] :: values.drop (k + 1) = values := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have fwd := scan (values.take k) values[k] (values.drop (k + 1)) streamTail [] resultTail
  have rev := restore streamTail (values[k] :: values.drop (k + 1)) (values.take k).reverse
    (values[k] :: resultTail)
  simp only [length_pre, split, List.append_nil] at fwd
  simp only [List.length_reverse, List.reverse_reverse, length_pre, split] at rev
  simpa only [show 3 * k + 4 + (2 * k + 1) = 5 * k + 5 by omega] using fwd.trans rev

/-- A normal lookup returns to its caller. The malformed-input halt still rejects. -/
def routine : FiniteRoutine Port := FiniteRoutine.ofStackCode code id .index (fun q => decide (q = .done))

theorem routine_runs (values streamTail resultTail : List Bool) (k : ℕ) (hk : k < values.length) :
    routine.Runs (5 * k + 5)
      (store (List.replicate k true ++ false :: streamTail) values [] resultTail)
      (store streamTail values [] (values[k] :: resultTail)) := by
  apply FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl rfl
    (fun q h => by simp only [decide_eq_true_eq] at h; subst q; rfl) (lookup_runs ..)
  · exact fun _ => rfl
  · exact fun _ => rfl
  · intro q h
    exact (h q rfl).elim

end RAMTape.AdviceBitLookup

end VPVNP
end Computability
end OAI
