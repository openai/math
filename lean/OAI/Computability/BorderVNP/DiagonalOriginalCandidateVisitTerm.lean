import OAI.Computability.BorderVNP.DiagonalOriginalObservedCandidateReports

/-! # The report candidate on its attained original visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term

private def originalInputs (proof : Expr) (service : Name) : MetaM Expr := do
  let some type ← whnfUntil (← inferType proof) service |
    throwError "expected an application of {service}"
  return type

/-- Apply the original-visit theorem to the returned builder, the observed
owner and the equality identifying its native prefix. -/
elab (name := sourceCandidateAtVisit) "sourceCandidateAtVisit% " candidate:term:max observed:term:max attained:term:max : term => do
  let returned ← elabTerm candidate none
  let route ← elabTerm observed none
  let visited ← elabTerm attained none
  let requests := [(`K,returned,``PreparationFrame.CandidateReportsOnReplay),
    (`seen,route,``PreparationFrame.OwnedRouteOn),(`atVisit,visited,``Eq)]
  let method := ``PreparationFrame.CandidateReportsOnReplay.atOriginalVisit
  let signature ← getConstInfo method
  let scheme ← originalInputs returned ``PreparationFrame.CandidateReportsOnReplay
  let source ← getConstInfo ``PreparationFrame.CandidateReportsOnReplay
  let recordedLevels := source.levelParams.zip scheme.getAppFn.constLevels!
  let levels ← signature.levelParams.mapM fun name => do
    let some level := recordedLevels.lookup name | throwError "missing universe {name}"
    return level
  forallTelescope signature.type fun parameters _ => do
    let names ← parameters.mapM fun p => p.fvarId!.getUserName
    let mut patterns := #[]
    let mut values := #[]
    for (label,value,head) in requests do
      let some pos := names.idxOf? label | throwError "missing the original parameter {label}"
      patterns := patterns ++ (← originalInputs parameters[pos]! head).getAppArgs
      values := values ++ (← originalInputs value head).getAppArgs
    let args ← parameters.mapM fun p => do
      let name ← p.fvarId!.getUserName
      if let some item := requests.find? (fun row => row.1 == name) then return item.2.1
      let some i := patterns.findIdx? (· == p) | throwError "missing the recorded parameter {name}"
      return values[i]!
    return mkAppN (mkConst method levels) args

end TeamContraction

end BorderVNP
end Computability
end OAI
