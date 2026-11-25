import OAI.Computability.BorderVNP.DiagonalSelectedCandidateWriterTerm

/-! # The label entering a selected physical writer's declared team weights -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Elab Term Meta RoutingISA.Evaluator.SignedPrep Cube.Physical

private def writerArgument (e : Expr) (head : Name) (field : Name) : MetaM Expr := do
  let some app ← whnfUntil e head | throwError "expected {head}"
  let info ← getConstInfo head
  forallTelescope info.type fun fields _ => do
    let some i ← fields.findIdxM? fun v => return (← v.fvarId!.getUserName) == field
      | throwError "missing {field}"
    return app.getAppArgs[i]!

/-- Read the original label used to compute this actual site's team for a
declared group. The computed and expanded forms both contain the same label. -/
elab "physicalWriterLabel%" evidence:term:max : term => do
  let evidence ← elabTerm evidence none
  forallBoundedTelescope (← inferType evidence) (some 3) fun bs _ => do
    unless bs.size == 3 do throwError "expected an exterior, a team and its signed site"
    let group ← writerArgument (← inferType bs[2]!) ``CandidateSite `group
    if group.isAppOf ``declaredTeam then
      return ← writerArgument group ``declaredTeam `label
    lambdaTelescope (← whnf group) fun _ output => do
      let weights ← writerArgument output ``Cube.TeamNative.owner `ws
      writerArgument weights ``declarationWeight `label

end TeamContraction

end BorderVNP
end Computability
end OAI
