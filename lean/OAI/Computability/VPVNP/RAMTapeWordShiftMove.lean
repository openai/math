import OAI.Computability.VPVNP.RAMTapeWordShiftControl

/-!
# Stack transfers in the variable-shift machine

Each transfer pops the source and pushes its bits onto the destination.
The final empty-stack test accounts for one step beyond the two steps per
bit. Discarding the remaining shift amount needs only the pops.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Shift

open RAMTape

local macro "move_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_store])

local macro "transfer_stack " src:Lean.Parser.Tactic.elimTarget " into " dst:ident : tactic => `(tactic|
  induction $src generalizing $dst with
  | nil => move_step; exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    move_step
    move_step
    exact ih (b :: $dst))

theorem prepare_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (2 * t.length + 1) .prepare (store a d t o s)
      .loop (store a (t.reverse ++ d) [] o s) := by
  transfer_stack t into d

theorem reverseData_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (2 * d.length + 1) .reverseData (store a d t o s)
      .restoreData (store a [] (d.reverse ++ t) o s) := by
  transfer_stack d into t

theorem restoreData_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (2 * t.length + 1) .restoreData (store a d t o s)
      .finish (store a d [] (t.reverse ++ o) s) := by
  transfer_stack t into o

theorem reverseOut_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (2 * o.length + 1) .reverseOut (store a d t o s)
      .done (store a d (o.reverse ++ t) [] s) := by
  transfer_stack o into t

theorem discard_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (a.length + 1) .discard (store a d t o s)
      .finish (store [] d t o s) := by
  induction a with
  | nil => move_step; exact .nil ..
  | cons b a ih =>
    simp only [List.length_cons]
    move_step
    exact ih

end TapeWord.Shift

end VPVNP
end Computability
end OAI
