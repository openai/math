import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Reading the monomial of an affine pin row from its packed exponent bits

The low bit of the selected variable has a known offset in the packed
exponent array. A single scan distinguishes the zero vector, the vector
with just this one low bit set, and all other bit patterns. The scan
consumes the exponent scratch buffer and the unary offset. It returns
one bit for each of the two distinguished cases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Exponents

open RAMTape

/-- Input stacks for the packed exponents and unary offset, with output stacks for the constant
and unit-monomial flags. -/
inductive Port where | exponents | offset | constant | unit
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Classify the monomial at coordinate `i` as the constant monomial, the variable `X i`, or a
different monomial. -/
inductive Kind where | constant | unit | other
  deriving DecidableEq

instance : Fintype Kind := derive_fintype% _

/-- Control states for scanning to the selected exponent bit, checking the remaining bits, and
emitting the two classification flags. -/
inductive State where
  | before (nonzero : Bool) | skip (nonzero : Bool) | select (nonzero : Bool)
  | after (kind : Kind) | writeUnit (kind : Kind) | writeConstant (kind : Kind) | done | reject
  deriving DecidableEq, Fintype

/-- Classify the prefix ending at the low bit of the selected coordinate. A previous nonzero
bit forces the other case. -/
def selected (before bit : Bool) : Kind :=
  if before then .other else if bit then .unit else .constant

/-- Retain the prefix classification when every remaining exponent bit is false, and classify
the monomial as other when a true bit occurs. -/
def tailKind (kind : Kind) (tail : List Bool) : Kind := if true ∈ tail then .other else kind

/-- Stack instructions that consume the unary offset and packed exponents and write the
constant and selected-unit flags. -/
def code : StackCode Port State
  | .before b => .pop .offset (fun v => v.elim (.select b) fun t => if t then .skip b else .reject)
  | .skip b => .pop .exponents (fun v => v.elim .reject fun t => .before (b || t))
  | .select b => .pop .exponents (fun v => v.elim .reject fun t => .after (selected b t))
  | .after k => .pop .exponents (fun v => v.elim (.writeUnit k) fun t => .after (if t then .other else k))
  | .writeUnit k => .push .unit (decide (k = .unit)) (.writeConstant k)
  | .writeConstant k => .push .constant (decide (k = .constant)) .done
  | .done => .halt true
  | .reject => .halt false

/-- Place the exponent bit stream, offset markers, and existing flag-stack contents on the four
classifier ports. -/
def bank (exponents marks zero one : List Bool) : Stacks Port
  | .exponents => exponents
  | .offset => marks
  | .constant => zero
  | .unit => one

private theorem set_bank (a m z u xs : List Bool) (p : Port) :
    Function.update (bank a m z u) p xs = match p with
      | .exponents => bank xs m z u | .offset => bank a xs z u
      | .constant => bank a m xs u | .unit => bank a m z xs := by
  cases p <;> funext i <;> cases i <;> rfl

local macro "pin_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, set_bank, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, Option.elim_some, Option.elim_none, ite_true, ite_false])

private theorem skip_runs (pre xs z u : List Bool) (b : Bool) :
    StackRuns code (2*pre.length+1) (.before b)
      (bank (pre++xs) (List.replicate pre.length true) z u)
      (.select (b || decide (true ∈ pre))) (bank xs [] z u) := by
  induction pre generalizing b with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append, List.replicate_zero,
      List.not_mem_nil, decide_false, Bool.or_false]
    pin_step
    exact .nil ..
  | cons t pre ih =>
    simp only [List.length_cons, Nat.mul_succ, List.cons_append, List.replicate_succ]
    pin_step
    pin_step
    cases t <;> cases b <;> by_cases ht : true ∈ pre <;> simpa [ht] using ih _

private theorem after_runs (xs z u : List Bool) (k : Kind) :
    StackRuns code (xs.length+3) (.after k) (bank xs [] z u) .done
      (bank [] [] (decide (tailKind k xs = .constant) :: z) (decide (tailKind k xs = .unit) :: u)) := by
  induction xs generalizing k with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, tailKind, List.not_mem_nil, ite_false]
    pin_step
    pin_step
    pin_step
    exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons]
    pin_step
    cases b with
    | false => by_cases hx : true ∈ xs <;> simpa [tailKind, hx] using ih k
    | true => simpa [tailKind] using ih .other

/-- Run the packed-exponent classifier from an empty scanned prefix and return after writing
both flags. -/
def machine : FiniteRoutine Port := .ofStackCode code id (.before false) (· == .done)

/-- Zero except possibly at the selected bit gives the constant or linear
coefficient. A nonzero bit anywhere else gives the zero coefficient. -/
def classify (pre : List Bool) (bit : Bool) (post : List Bool) : Kind :=
  tailKind (selected (decide (true ∈ pre)) bit) post

theorem machine_runs (pre : List Bool) (bit : Bool) (post z u : List Bool) :
    let k := classify pre bit post
    machine.Runs (2*pre.length + post.length + 5)
      (bank (pre ++ bit::post) (List.replicate pre.length true) z u)
      (bank [] [] (decide (k = .constant)::z) (decide (k = .unit)::u)) := by
  dsimp only
  have skip := skip_runs pre (bit::post) z u false
  rw [Bool.false_or] at skip
  have low : StackRuns code 1 (.select (decide (true ∈ pre))) (bank (bit::post) [] z u)
      (.after (selected (decide (true ∈ pre)) bit)) (bank post [] z u) := by
    pin_step
    exact .nil ..
  have hr := (skip.trans low).trans (after_runs post z u _)
  rw [show 2*pre.length + 1 + 1 + (post.length+3) = 2*pre.length + post.length+5 by omega] at hr
  exact FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl rfl
    (fun q h => by cases q <;> simp_all [code]) hr (fun _ => rfl) (fun _ => rfl)
    (fun j hj => (hj j rfl).elim)

end AffinePin.Exponents

end VPVNP
end Computability
end OAI
