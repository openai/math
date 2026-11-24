import OAI.Computability.VPVNP.RAMTapeSuccessors
import OAI.Computability.VPVNP.StructuredStackCount
import OAI.Computability.VPVNP.StructuredStackTotal

/-!
# Rejecting malformed successor fields

The field reader produces separate validity bits for the send and receive.
The guard consumes those bits, continues only when both are true, and
otherwise halts with rejection. This instruction table can be linked directly
to the processor's call loop.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMSerialization RAMLayout

/-- States for testing the send and receive verdicts and halting on a failed test. -/
inductive GuardState where | send | receive | reject
  deriving DecidableEq

instance : Fintype GuardState := derive_fintype% _

/-- Consume the send verdict followed by the receive verdict, continuing only if both are
present and true. -/
def guard : FiniteRoutine Port := FiniteRoutine.ofRoutine ({
  entry := .send
  code
    | .send => .pop (.verdict .send) fun b ↦ if b = some true then some .receive else some .reject
    | .receive => .pop (.verdict .receive) fun b ↦ if b = some true then none else some .reject
    | .reject => .halt false
  } : Routine Port GuardState)

/-- Read the two successor fields and then guard the continuation with both validity bits. -/
def checked : FiniteRoutine Port := read.followedBy guard

/-- Pop the send and receive verdict stacks after a successful guard. -/
def guardResult (s : Stacks Port) : Stacks Port :=
  Function.update (Function.update s (.verdict .send) (s (.verdict .send)).tail)
    (.verdict .receive) (s (.verdict .receive)).tail

theorem guard_runs (s : Stacks Port) (hs : (s (.verdict .send)).head? = some true)
    (hr : (s (.verdict .receive)).head? = some true) : guard.Runs 2 s (guardResult s) := by
  let t := Function.update s (.verdict .send) (s (.verdict .send)).tail
  have hs' : StackStep guard.body.standalone (some GuardState.send) s (some GuardState.receive) t := by
    simpa only [hs, ite_true] using (StackStep.pop (s := s) (code := guard.body.standalone)
      (show guard.body.standalone (some GuardState.send) = .pop (.verdict .send)
        (fun b ↦ if b = some true then some GuardState.receive else some GuardState.reject) from rfl))
  have ht : t (.verdict .receive) = s (.verdict .receive) := rfl
  have hr' : StackStep guard.body.standalone (some GuardState.receive) t none (guardResult s) := by
    simpa only [ht, hr, ite_true, guardResult, t] using (StackStep.pop (s := t) (code := guard.body.standalone)
      (show guard.body.standalone (some GuardState.receive) = .pop (.verdict .receive)
        (fun b ↦ if b = some true then none else some GuardState.reject) from rfl))
  exact .cons hs' (.cons hr' (.nil ..))

theorem guard_count (s : Stacks Port) (c : ℕ → Stacks Port → ℕ) (fuel : ℕ) :
    guard.body.count c (fuel+2) s =
      if (s (.verdict .send)).head? = some true ∧ (s (.verdict .receive)).head? = some true
      then c fuel (guardResult s) else 0 := by
  by_cases hs : (s (.verdict .send)).head? = some true
  · by_cases hr : (s (.verdict .receive)).head? = some true
    · simpa [hs, hr] using (guard_runs s hs hr).count_eq c fuel
    · cases fuel <;> simp [Routine.count, Routine.countFrom, guard, FiniteRoutine.ofRoutine,
        hs, hr]
  · simp [Routine.count, Routine.countFrom, guard, FiniteRoutine.ofRoutine, hs]

theorem checked_count_of_read {s out : Stacks Port} {n : ℕ} (h : read.Runs n s out)
    (c : ℕ → Stacks Port → ℕ) (fuel : ℕ) :
    checked.body.count c (fuel + 2 + n) s =
      if (out (.verdict .send)).head? = some true ∧ (out (.verdict .receive)).head? = some true
      then c fuel (guardResult out) else 0 := by
  change (read.body.followedBy guard.body).count _ _ _ = _
  rw [Routine.count_followedBy, h.count_eq, guard_count]

/-- The third guard instruction suffices even when the second validity bit
is false and the explicit rejecting halt must still execute. -/
theorem checked_allStops_of_read {s out : Stacks Port} {n : ℕ} (h : read.Runs n s out)
    (c : ℕ → Stacks Port → Prop) (fuel : ℕ) :
    checked.body.AllStops c (fuel + 3 + n) s ↔
      ((out (.verdict .send)).head? = some true ∧ (out (.verdict .receive)).head? = some true →
        c (fuel + 1) (guardResult out)) := by
  change (read.body.followedBy guard.body).AllStops _ _ _ ↔ _
  rw [Routine.allStops_followedBy, h.allStops_iff]
  by_cases hs : (out (.verdict .send)).head? = some true
  · by_cases hr : (out (.verdict .receive)).head? = some true
    · simpa [hs, hr] using (guard_runs out hs hr).allStops_iff c (fuel+1)
    · simp [Routine.AllStops, Routine.AllStopsFrom, guard, FiniteRoutine.ofRoutine, hs, hr]
  · simp [Routine.AllStops, Routine.AllStopsFrom, guard, FiniteRoutine.ofRoutine, hs]

end RAMTape.Successors

end VPVNP
end Computability
end OAI
