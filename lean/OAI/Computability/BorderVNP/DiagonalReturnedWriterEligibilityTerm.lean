import Lean

/-! # Applying the eligibility test to the actual writer observation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term Tactic

/-- Pair the observed range proof with the forward direction of the
eligibility equivalence, applied to the native capacity observation.
Its two middle propositions are checked by the kernel on the issued data. -/
private def fromRegisteredEligibility (guard eligible : Expr) : MetaM Expr := do
  let some tests ← whnfUntil (← inferType guard) ``And
    | throwError "expected the returned native range and capacity proofs"
  let some equivalence ← whnfUntil (← inferType eligible) ``Iff
    | throwError "expected the original declaration's eligibility equivalence"
  let sides := equivalence.getAppArgs
  let accepted := mkAppN (Lean.mkConst ``Iff.mp) #[sides[0]!, sides[1]!, eligible, .proj ``And 1 guard]
  return mkAppN (Lean.mkConst ``And.intro) #[tests.getAppArgs[0]!, sides[1]!, .proj ``And 0 guard, accepted]

/-- Apply the checked original eligibility test to the actual writer's
range and capacity observations. -/
elab "registeredEligibility% " guard:term:max eligible:term:max : term => do
  fromRegisteredEligibility (← Term.elabTerm guard none) (← Term.elabTerm eligible none)

/-- Finish the original range and eligibility goal with the proof carried by
the returned writer. -/
elab "close_registered_eligibility " guard:term:max eligible:term:max : tactic => withMainContext do
  let result ← fromRegisteredEligibility (← Term.elabTerm guard none) (← Term.elabTerm eligible none)
  (← getMainGoal).assign result
  replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
