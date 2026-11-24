import OAI.Computability.VPVNP.StructuredStacks
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Enumerating the labels in an evaluator column

The remaining labels are counted in unary. The body sees the index of the
current label, starting at zero. Each normal return increments the index
before the next iteration. At the end of the column the loop clears the
index for reuse on the next column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorTallyLoop

open RAMTape

/-- Control states for the unary label loop, including the callback, index advancement, final
index clearing and rejection. -/
inductive State (Q : Type*) where
  | scan | call (q : Q) | advance | clearIndex | reject
  deriving Fintype

variable {K Q : Type*}

/-- A zero bit in the unary count rejects. The body is invoked once per mark. -/
def tallyLoop (remain index : K) (body : Routine K Q) : Routine K (State Q) where
  entry := .scan
  code
    | .scan => .pop remain fun b => some <| match b with
      | none => .clearIndex
      | some false => .reject
      | some true => .call body.entry
    | .call q => body.install State.call (some .advance) q
    | .advance => .push index true (some .scan)
    | .clearIndex => .pop index fun b => b.map fun _ => .clearIndex
    | .reject => .halt false

variable [DecidableEq K] (remain index : K) (body : Routine K Q) (c : ℕ → Stacks K → ℕ)

private theorem advance_count :
    (fun n s => (tallyLoop remain index body).countFrom c n (some .advance) s) =
      (Routine.push index true).count ((tallyLoop remain index body).count c) := by
  funext n s
  cases n <;> simp only [Routine.count, Routine.countFrom, Routine.push, tallyLoop, Routine.countFrom_none]

/-- Reading one mark costs one instruction. Each path through the body spends
one further instruction to push the index mark if it returns normally. -/
theorem loop_count_succ (s : Stacks K) (tail : List Bool) (hs : s remain = true :: tail) (fuel : ℕ) :
    (tallyLoop remain index body).count c (fuel+1) s =
      body.count ((Routine.push index true).count ((tallyLoop remain index body).count c)) fuel
        (Function.update s remain tail) := by
  have h := Routine.countFrom_install (tallyLoop remain index body) body State.call (some .advance)
    (fun _ => rfl) c fuel (some body.entry) (Function.update s remain tail)
  rw [advance_count] at h
  simpa only [Routine.count, Routine.countFrom, tallyLoop, hs, List.head?_cons, List.tail_cons,
    Option.elim_some, Function.comp_apply] using h

private theorem clear_count (s : Stacks K) (xs : List Bool) (hs : s index = xs) (fuel : ℕ) :
    (tallyLoop remain index body).countFrom c (fuel+xs.length+1) (some .clearIndex) s =
      c fuel (Function.update s index []) := by
  induction xs generalizing s with
  | nil => simp [Routine.countFrom, tallyLoop, hs]
  | cons b xs ih =>
    simp only [Routine.countFrom, tallyLoop, hs, List.head?_cons, List.tail_cons, Option.map_some]
    have h := ih (Function.update s index xs) (Function.update_self ..)
    simpa only [tallyLoop, List.length_cons, Nat.add_assoc, Function.update_idem] using h

/-- The empty test, one pop per used index mark, and the last empty index
test return to the caller, preserving every stack other than the index. -/
theorem loop_count_zero (s : Stacks K) (hs : s remain = []) (fuel : ℕ) :
    (tallyLoop remain index body).count c (fuel+(s index).length+2) s =
      c fuel (Function.update s index []) := by
  have hu : Function.update s remain [] = s := hs ▸ Function.update_eq_self remain s
  simpa only [Routine.count, Routine.countFrom, tallyLoop, hs, List.head?_nil, List.tail_nil, hu] using
    clear_count remain index body c s (s index) rfl fuel

end EvaluatorTallyLoop

end VPVNP
end Computability
end OAI
