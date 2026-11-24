import OAI.Computability.VPVNP.RAMProcessorFlow

/-!
# A deterministic payload after a two-exit processor fragment

A successful test enters the payload without an extra transition. Rejection
jumps directly to its caller label, leaving the rejected branch's stack state
available to the caller.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Fragment

variable {K L : Type}

private def guardedLabel (guard : Fragment K Bool) (payload : FiniteRoutine K) (bad : L) :
    guard.State ⊕ Bool → (guard.State ⊕ payload.State) ⊕ L
  | .inl q => .inl (.inl q)
  | .inr true => .inl (.inr payload.body.entry)
  | .inr false => .inr bad

private def payloadLabel (guard : Fragment K Bool) (payload : FiniteRoutine K) (good : L) :
    Option payload.State → (guard.State ⊕ payload.State) ⊕ L :=
  fun r => r.elim (.inr good) (Sum.inl ∘ Sum.inr)

/-- Link a Boolean guard to a returning payload. Success enters the payload and a failed guard
transfers directly to the rejection label. -/
def withPayload (guard : Fragment K Bool) (payload : FiniteRoutine K) (good bad : L) : Fragment K L where
  State := guard.State ⊕ payload.State
  entry := .inl guard.entry
  code
    | .inl q => (guard.code q).rename id (guardedLabel guard payload bad)
    | .inr q => (payload.body.code q).rename id (payloadLabel guard payload good)

variable [DecidableEq K]

private theorem guard_run {guard : Fragment K Bool} (payload : FiniteRoutine K) (good bad : L)
    {t s b u} (h : guard.Runs t s b u) :
    StackRuns (guard.withPayload payload good bad).isolated t
      (.inl (guard.withPayload payload good bad).entry) s (guardedLabel guard payload bad (.inr b)) u := by
  have hh (q : guard.State ⊕ Bool) (hn : (guard.isolated q).returns = false) :
      (guard.withPayload payload good bad).isolated (guardedLabel guard payload bad q) =
        (guard.isolated q).rename id (guardedLabel guard payload bad) := by
    cases q with
    | inl => rfl
    | inr => contradiction
  have run := h.lift id Function.injective_id (guardedLabel guard payload bad) s hh
  have same (v : Stacks K) : installStacks id s v = v := by
    funext j; exact installStacks_at Function.injective_id s v j
  rw [same, same] at run
  exact run

theorem withPayload_reject {guard : Fragment K Bool} (payload : FiniteRoutine K) (good bad : L)
    {t s u} (h : guard.Runs t s false u) :
    (guard.withPayload payload good bad).Runs t s bad u := guard_run payload good bad h

theorem withPayload_ok {guard : Fragment K Bool} {payload : FiniteRoutine K} (good bad : L)
    {t m s mid u} (test : guard.Runs t s true mid) (h : payload.Runs m mid u) :
    (guard.withPayload payload good bad).Runs (t+m) s good u := by
  have hh (q : Option payload.State) (hn : (payload.body.standalone q).returns = false) :
      (guard.withPayload payload good bad).isolated (payloadLabel guard payload good q) =
        (payload.body.standalone q).rename id (payloadLabel guard payload good) := by
    cases q with
    | none => contradiction
    | some => rfl
  have run := h.lift id Function.injective_id (payloadLabel guard payload good) mid hh
  have same (v : Stacks K) : installStacks id mid v = v := by
    funext j; exact installStacks_at Function.injective_id mid v j
  rw [same, same] at run
  exact (guard_run payload good bad test).trans run

end RAMTape.Fragment

end VPVNP
end Computability
end OAI
