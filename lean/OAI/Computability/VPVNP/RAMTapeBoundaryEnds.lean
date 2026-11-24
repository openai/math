import OAI.Computability.VPVNP.RAMTapeBoundaryControl

/-!
# Restoring a record and checking zero boundary messages

The incoming edge check saves each inspected bit so that the usual restore
loop reconstructs the predecessor. The outgoing edge check consumes its
message. Each check accumulates the zero test in a single control bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

local macro "boundary_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, update_store, List.head?_cons, List.tail_cons, List.head?_nil,
    List.tail_nil, Option.elim_some, Option.elim_none])

/-- Return the saved slot to the predecessor stack, reversing the order in
which its bits were pushed during the scan. -/
theorem restoreSlot_runs (hasPrev hasNext : Bool) (m : Mode) (ok : Bool)
    (block previous sent width widthBack saved slots : List Bool) :
    StackRuns (code hasPrev hasNext) (2 * saved.length + 1) (.restoreSlot m ok)
      (store block previous sent width widthBack saved slots)
      (if m = .row then .next ok else .done ok)
      (store block (saved.reverse ++ previous) sent width widthBack [] slots) := by
  induction saved generalizing previous with
  | nil => boundary_step; exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    boundary_step
    boundary_step
    exact ih (b :: previous)

/-- Check an incoming boundary message and save the inspected bits. -/
theorem checkPrev_runs (hasPrev hasNext ok : Bool)
    (block previous sent width widthBack saved slots : List Bool) :
    StackRuns (code hasPrev hasNext) (2 * previous.length + 1) (.checkPrev ok)
      (store block previous sent width widthBack saved slots)
      (.restoreSlot .row (ok && previous.all (!·)))
      (store block [] sent width widthBack (previous.reverse ++ saved) slots) := by
  induction previous generalizing saved ok with
  | nil =>
    simp only [List.all_nil, Bool.and_true]
    boundary_step
    exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.all_cons, ← Bool.and_assoc]
    boundary_step
    boundary_step
    exact ih (ok && !b) (b :: saved)

/-- Check an outgoing boundary message and consume its bit stream. -/
theorem checkSent_runs (hasPrev hasNext ok : Bool)
    (block previous sent width widthBack saved slots : List Bool) :
    StackRuns (code hasPrev hasNext) (sent.length + 1) (.checkSent ok)
      (store block previous sent width widthBack saved slots)
      (.done (ok && sent.all (!·))) (store block previous [] width widthBack saved slots) := by
  induction sent generalizing ok with
  | nil =>
    simp only [List.all_nil, Bool.and_true]
    boundary_step
    exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, List.all_cons, ← Bool.and_assoc]
    boundary_step
    exact ih (ok && !b)

end RAMTape.Boundary

end VPVNP
end Computability
end OAI
