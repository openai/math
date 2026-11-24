import OAI.Computability.VPVNP.RAMTapeISAPorts

/-!
# Returning the result bit of a circuit evaluation

The interpreter leaves the last gate value on top of the stack of intermediate
values. The caller needs that one bit on its result stack and the valuation
stack empty for the next evaluation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AdviceReturnBit

private inductive Control where
  | read | drain (bit : Bool) | write (bit : Bool) | reject
  deriving Fintype

variable {K : Type}

private def body (src dst : K) : Routine K Control where
  entry := .read
  code
    | .read => .pop src fun b => some (b.elim .reject .drain)
    | .drain bit => .pop src fun b => some (b.elim (.write bit) fun _ => .drain bit)
    | .write bit => .push dst bit none
    | .reject => .halt false

/-- Save the head bit, drain the source stack and prepend that bit to the
destination. An empty source rejects. -/
def takeTopAndClear (src dst : K) : FiniteRoutine K := .ofRoutine (body src dst)

variable [DecidableEq K] {src dst : K}

private theorem drain_runs (hne : src ≠ dst) (s : Stacks K) (bit : Bool) (tail : List Bool) :
    StackRuns (body src dst).standalone (tail.length + 2) (some (.drain bit))
      (Function.update s src tail) none (Function.update (Function.update s src []) dst (bit :: s dst)) := by
  induction tail with
  | nil =>
    apply StackRuns.cons (.pop rfl)
    simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.elim_none, Function.update_idem]
    simpa only [List.length_nil, Function.update_of_ne hne.symm] using
      (StackRuns.cons (StackStep.push (code := (body src dst).standalone) (s := Function.update s src [])
        (q := some (.write bit)) rfl) (.nil ..))
  | cons b tail ih =>
    apply StackRuns.cons (.pop rfl)
    simpa only [List.length_cons, Function.update_self, List.head?_cons, List.tail_cons, Option.elim_some,
      Function.update_idem] using ih

/-- Each discarded bit costs one pop. The other three steps read the answer,
test the empty source and push the answer on the destination. -/
theorem takeTopAndClear_runs (hne : src ≠ dst) (s : Stacks K) (bit : Bool) (tail : List Bool)
    (hsrc : s src = bit :: tail) :
    (takeTopAndClear src dst).Runs (tail.length + 3) s
      (Function.update (Function.update s src []) dst (bit :: s dst)) := by
  change StackRuns (body src dst).standalone _ (some .read) s none _
  apply StackRuns.cons (.pop rfl)
  simpa only [hsrc, List.head?_cons, List.tail_cons, Option.elim_some] using drain_runs hne s bit tail

end RAMTape.AdviceReturnBit

end VPVNP
end Computability
end OAI
