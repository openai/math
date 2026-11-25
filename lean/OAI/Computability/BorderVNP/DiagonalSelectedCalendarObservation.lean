import Lean

/-! # Applying an observation to the original calendar lookup inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

private partial def storedLookupTerm (termValue : Expr) : MetaM Expr := do
  let actual := termValue.consumeMData
  if actual.isFVar then
    if let some value ← actual.fvarId!.getValue? then return ← storedLookupTerm value
  return actual

/-- Apply a calendar observation with the same parameter prefix as the attained lookup.
The frame, settings and witnesses come from that lookup's original application. Any
remaining inputs of the observation can then be supplied at the corresponding return. -/
syntax "onReturnedCalendar% " term:max " for " ident (" at " "[" term,* "]")? : term

elab_rules : term
  | `(onReturnedCalendar% $source for $observation $[at [$[$additional],*]]?) => do
    let application ← storedLookupTerm (← elabTerm source none)
    unless application.isAppOf `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.frozenLookupAt do
      throwError "expected the original frozen calendar lookup"
    let observer ← resolveGlobalConstNoOverload observation
    let levels := application.getAppFn.constLevels!
    unless (← getConstInfo observer).levelParams.length == levels.length do
      throwError "the observation and the original lookup have different universe parameters"
    let partialCall := mkAppN (mkConst observer levels) application.getAppArgs
    match additional with
    | none => return partialCall
    | some terms => return mkAppN partialCall (← terms.mapM fun t => elabTerm t none)

end Diagonal

end BorderVNP
end Computability
end OAI
