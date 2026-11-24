import OAI.Computability.VPVNP.EvaluatorDigitCallbacks
import OAI.Computability.VPVNP.RankQueryStackEngineSpec

/-!
# The product-loop counter test in the Schur controller

A zero counter is consumed and yields a true completion flag. A positive
counter loses one, keeps its width, and yields a false completion flag.
The control scans the low zero bits only and reuses one empty scratch stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine.Borrow

open RAMTape UniversalCountStack TapeWord

/-- Counter, borrow scratch stack and completion flag used by the binary decrement routine. -/
inductive Port where | counter | scratch | flag deriving DecidableEq
instance : Fintype Port := derive_fintype% _

/-- Control phases for scanning low bits, resolving a borrow and reporting whether the counter
was exhausted. -/
inductive Phase where
  | scan | save | lower | restore | raise | discard | signal (finished : Bool)
  deriving DecidableEq, Fintype

/-- Decrement a positive little-endian counter by borrowing through its low zero bits, or
signal completion when the counter is zero. -/
def body : Routine Port Phase where
  entry := .scan
  code
    | .scan => .pop .counter fun b => some (b.elim .discard fun d => if d then .lower else .save)
    | .save => .push .scratch true (some .scan)
    | .lower => .push .counter false (some .restore)
    | .restore => .pop .scratch fun b => some (if b.isSome then .raise else .signal false)
    | .raise => .push .counter true (some .restore)
    | .discard => .pop .scratch fun b => some (if b.isSome then .discard else .signal true)
    | .signal b => .push .flag b none

/-- Assign the counter bits, scratch contents and flag bits to their three respective ports. -/
def bank (counter scratch flag : List Bool) : Stacks Port
  | .counter => counter | .scratch => scratch | .flag => flag

private theorem update_bank (x t f y : List Bool) (k : Port) :
    Function.update (bank x t f) k y = match k with
      | .counter => bank y t f | .scratch => bank x y f | .flag => bank x t y := by
  funext j; cases k <;> cases j <;> rfl

local macro "borrow_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, update_bank, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
    Option.elim_none, Option.elim_some, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ite_false, ite_true])

private theorem move_true (l : ℕ) (xs : List Bool) :
    List.replicate l true ++ true :: xs = true :: (List.replicate l true ++ xs) := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [List.replicate_succ, List.cons_append, ih]

private theorem scan (l : ℕ) (tail t : List Bool) :
    StackRuns body.standalone (2*l) (some .scan) (bank (List.replicate l false ++ tail) t [])
      (some .scan) (bank tail (List.replicate l true ++ t) []) := by
  induction l generalizing t with
  | zero => exact .nil ..
  | succ l ih =>
    simp only [Nat.mul_succ, List.replicate_succ, List.cons_append]
    borrow_step
    borrow_step
    simpa only [move_true] using ih (true :: t)

private theorem restore (l : ℕ) (x : List Bool) :
    StackRuns body.standalone (2*l+2) (some .restore) (bank x (List.replicate l true) [])
      none (bank (List.replicate l true ++ x) [] [false]) := by
  induction l generalizing x with
  | zero => borrow_step; borrow_step; exact .nil ..
  | succ l ih =>
    simp only [Nat.mul_succ, List.replicate_succ, List.cons_append]
    borrow_step
    borrow_step
    simpa only [move_true] using ih (true :: x)

private theorem discard (l : ℕ) : StackRuns body.standalone (l+2) (some .discard)
    (bank [] (List.replicate l true) []) none (bank [] [] [true]) := by
  induction l with
  | zero => borrow_step; borrow_step; exact .nil ..
  | succ l ih =>
    simp only [List.replicate_succ]
    borrow_step
    exact ih

theorem zero_runs (w : ℕ) : body.Runs (3*w+3) (bank (digits w 0) [] []) (bank [] [] [true]) := by
  rw [digits_zero]
  have first := scan w [] []
  simp only [List.append_nil] at first
  have rest : StackRuns body.standalone ((w+2)+1) (some .scan) (bank [] (List.replicate w true) [])
      none (bank [] [] [true]) := by borrow_step; exact discard w
  convert first.trans rest using 1 <;> first | rfl | omega

theorem succ_runs (w k : ℕ) (h : k+1 < 2^w) :
    ∃ t ≤ 4*w+4, body.Runs t (bank (digits w (k+1)) [] []) (bank (digits w k) [] [false]) := by
  have hv : value (digits w (k+1)) = k+1 := by simp [Nat.mod_eq_of_lt h]
  obtain ⟨l,tail,eq⟩ := EvaluatorDigitCallbacks.split_positive (digits w (k+1)) (by omega)
  have hl : l+tail.length+1 = w := by
    have hlen := congrArg List.length eq
    simp at hlen; omega
  have smaller : List.replicate l true ++ false :: tail = digits w k := by
    apply eq_of_length_value (by simp; omega)
    have := EvaluatorDigitRepeat.value_decrement l tail
    rw [← eq, hv] at this
    simp [Nat.mod_eq_of_lt (by omega : k < 2^w)]
    omega
  have first := scan l (true :: tail) []
  simp only [List.append_nil] at first
  have middle : StackRuns body.standalone 2 (some .scan) (bank (true :: tail) (List.replicate l true) [])
      (some .restore) (bank (false :: tail) (List.replicate l true) []) := by
    borrow_step; borrow_step; exact .nil ..
  have final := (first.trans middle).trans (restore l (false :: tail))
  rw [← eq, smaller] at final
  exact ⟨_, by omega, final⟩

end RankQuery.Stack.Engine.Borrow

end VPVNP
end Computability
end OAI
