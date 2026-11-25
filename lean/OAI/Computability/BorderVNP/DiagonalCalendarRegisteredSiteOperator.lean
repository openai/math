import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation
import OAI.Computability.BorderVNP.DiagonalCheckedRouteReadback
import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites

/-! # Selecting the installed publication of an original issued field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction TeamContraction.ProcessorSlots

/-- Read the next input type from a calibrated family of original fields or
their returned sites. -/
def SignedCalendarAt.nextIssuedInput (operator : Expr) : MetaM Expr := do
  let .forallE _ input _ _ ← whnf (← inferType operator)
    | throwError "expected a family on the original fields or their publication sites"
  return input

private def publicationArguments (siteType : Expr) : MetaM (Expr × Expr) := do
  let some site ← whnfUntil siteType ``PreparationFrame.SelectedLookupSites
    | throwError "expected the enrolled publication sites"
  let args := site.getAppArgs
  -- The preparation frame and its return predicate are the final site parameters.
  let frame := args[args.size-2]!
  unless frame.getAppFn.isConstOf ``AdmittedPinnedFrames.frame do
    throwError "expected the frame of the original admitted field"
  let params := frame.getAppArgs
  return (params[params.size-2]!, params.back!)

/-- Select the genuine returned site at an original field. The readback takes
the native pin, history and claim. The certificate takes the field and a site
on its enrolled frame. Both are specialized to the same calendar data. -/
def SignedCalendarAt.selectIssuedSite (readback certificate f : Expr) : MetaM Expr := do
  let (raw, granted) ← publicationArguments (← SignedCalendarAt.nextIssuedInput (mkApp certificate f))
  let records := mkProj ``Sigma 1 f
  let clauses := mkProj ``Sigma 1 records
  let checked := mkAppN readback #[mkProj ``Sigma 0 f, mkProj ``Sigma 0 records,
    mkProj ``Prod 0 (mkProj ``Sigma 1 clauses)]
  return mkApp2 (mkProj ``CheckedRouteReadback 1 checked) raw granted

/-- Apply an original-selection certificate to the arguments recorded by
`withCheckedRouteOperands`. The certificate takes the execution whose grid
appears in the route checks, followed by those same entries and checks. -/
def SignedCalendarAt.certifyOnCheckedCalendar (operation : Name) (inputs calibrated : Array Expr) :
    MetaM Expr := do
  let some executionIndex ← inputs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `oper)
    | throwError "expected the operative frozen calendar"
  let route ← getConstInfo ``SignedCalendarAt.FrozenRouteChecks
  let gridIndex ← forallTelescope route.type fun args _ => do
    let some i ← args.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `grid)
      | throwError "expected the frozen grid on this route"
    return i
  return mkAppN (← mkConstWithLevelParams operation) (calibrated.set! gridIndex inputs[executionIndex]!)

end Diagonal

end BorderVNP
end Computability
end OAI
