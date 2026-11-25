import OAI.Computability.BorderVNP.DiagonalCalendarNativeWriterOnOriginal
import OAI.Computability.BorderVNP.DiagonalRegisteredRoutedEnds
import OAI.Computability.BorderVNP.DiagonalCalendarOwnedHostWordsType

/-! # The original host reading after recovery of the complete registered route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta BorderVNP.Cube.Physical.NativeAssignments
set_option maxHeartbeats 2500000
set_option maxRecDepth 16000

private def originalReturnedHostIdentity : MetaM Expr := do
  let .defnInfo schema ← getConstInfo ``SignedCalendarAt.NativeOriginalWriterStatement |
    throwError "expected the original quantified writer return"
  forallTelescope schema.value fun inputs _ => do
    let some valueIndex ← inputs.findIdxM? (fun p => return (← p.fvarId!.getUserName) == `values) |
      throwError "missing the actual input matrices"
    let fieldValue := inputs.back!
    let history := mkProj ``Sigma 0 (mkProj ``Sigma 1 fieldValue)
    let calibrated := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRegisteredResidentCoordinates)
      ((inputs.extract 0 (valueIndex+1)).push history)
    let names := mkProj ``And 0 calibrated
    let produced := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenNativeWriterOnOriginal) inputs
    let complete := mkProj ``And 1 (mkProj ``And 0 (mkProj ``And 1 produced))
    let some spelling ← whnfUntil (← inferType complete) ``HEq | throwError "expected the entire observed route"
    let physical := spelling.getAppArgs[1]!
    let recover ← mkConstWithLevelParams ``Routed.atRegisteredOwner_eq
    let result ← forallTelescope (← inferType recover) fun args _ => do
      let mut nativeParams : Std.HashMap FVarId Expr := {}
      for (label,actual) in [(`physical,physical),(`names,names),(`same,complete)] do
        let some schemaParam ← args.findM? (fun x => return (← x.fvarId!.getUserName) == label) |
          throwError "missing native transport argument {label}"
        let schemaType ← inferType schemaParam
        let some typeName := schemaType.getAppFn.constName? | throwError "expected a routed type or equality"
        let some actualType ← whnfUntil (← inferType actual) typeName | throwError "expected actual {typeName}"
        nativeParams := nativeParams.insert schemaParam.fvarId! actual
        for abstractParam in schemaType.getAppArgs, actualParam in actualType.getAppArgs do
          if abstractParam.isFVar then nativeParams := nativeParams.insert abstractParam.fvarId! actualParam
      let arguments ← args.mapM fun x => do
        let some originalValue := nativeParams[x.fvarId!]? |
          throwError "actual route data missing {(←x.fvarId!.getUserName)}"
        return originalValue
      return mkAppN recover arguments
    let some routeEquality ← whnfUntil (← inferType result) ``Eq | throwError "expected the original routing identity"
    let visit := mkProj ``And 1 (mkProj ``And 0 produced)
    let some visitEquality ← whnfUntil (← inferType visit) ``Eq | throwError "expected the actual physical owner visit"
    let returned := visitEquality.getAppArgs[1]!
    let pin := mkProj ``Sigma 0 fieldValue
    let words ← mkConstWithLevelParams ``SignedCalendarAt.OwnedHostWords
    let predicate ← withLocalDeclD `submittedRoute routeEquality.getAppArgs[0]! fun route => do
      let reading := mkAppN words ((inputs.extract 0 (valueIndex+1)) ++ #[history,route,pin,returned])
      mkLambdaFVars #[route] reading
    mkLambdaFVars inputs (← mkCongrArg predicate result)

local elab "originalReturnedHostIdentityType%" : term => do inferType (← originalReturnedHostIdentity)

/-- Equality of the two host readings, for the original pin and the same physical
end of the owner exchange. All words of the routed payload are retained. -/
abbrev SignedCalendarAt.OriginalRegisteredHostIdentity : Prop := originalReturnedHostIdentityType%

/-- Transfer the host reading at the returned native route to the exact route submitted
with this original calendar field. -/
theorem SignedCalendarAt.frozenOriginalHostReadAtSubmitted : SignedCalendarAt.OriginalRegisteredHostIdentity := by
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.assign (←originalReturnedHostIdentity)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
