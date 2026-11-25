import OAI.Computability.BorderVNP.DiagonalCalendarOriginalHostCoordinate
import OAI.Computability.BorderVNP.DiagonalOriginalHostSourceReplay

/-! # The source reading at an original calendar owner's returned scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction BorderVNP.Cube.Physical.NativeAssignments
set_option maxHeartbeats 3600000
set_option maxRecDepth 18000

private def originalHostVisit : MetaM Expr := do
  let .defnInfo schema ← getConstInfo ``SignedCalendarAt.NativeOriginalWriterStatement |
    throwError "expected the original calendar inputs"
  forallTelescope schema.value fun inputs _ => do
    let physical := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenNativeWriterOnOriginal) inputs
    let returned := mkProj ``And 0 physical
    let seen := mkProj ``And 0 returned
    let atVisit := mkProj ``And 1 returned
    let recovered := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenOriginalHostReadAtSubmitted) inputs
    let some (_,left,_) := (← inferType recovered).eq? | throwError "expected the original host-reading equality"
    let some reading ← whnfUntil left ``SignedCalendarAt.OwnedHostWords | throwError "expected the source reading"
    let operands := reading.getAppArgs
    let routeIndex := operands.size-3
    let some route ← whnfUntil operands[routeIndex]! ``Routed.atRegisteredOwner |
      throwError "expected the returned route at its submitted owner"
    let routeArgs := route.getAppArgs
    let originalIndex := routeArgs.size-2
    let predicate ← withLocalDeclD `v (← inferType routeArgs[originalIndex]!) fun v => do
      withLocalDeclD `rows (← inferType operands.back!) fun rows => do
        let named := mkAppN route.getAppFn (routeArgs.set! originalIndex v)
        let property := mkAppN reading.getAppFn ((operands.set! routeIndex named).set! (operands.size-1) rows)
        mkLambdaFVars #[v,rows] property
    let visit ← mkConstWithLevelParams ``PreparationFrame.OwnedRouteOn.applyAtVisit
    let fromWriter ← forallTelescope (← inferType visit) fun binders _ => do
      let mut arguments : Std.HashMap FVarId Expr := {}
      for (name,data) in [(`seen,seen),(`atVisit,atVisit)] do
        let some parameter ← binders.findM? (fun b => return (← b.fvarId!.getUserName) == name) |
          throwError "missing owner visit operand {name}"
        let pattern ← inferType parameter
        let some head := pattern.getAppFn.constName? | throwError "expected a return or an equality"
        let some actual ← whnfUntil (← inferType data) head | throwError "expected the actual {head}"
        arguments := arguments.insert parameter.fvarId! data
        for formal in pattern.getAppArgs, original in actual.getAppArgs do
          if formal.isFVar then arguments := arguments.insert formal.fvarId! original
      let mut supplied := #[]
      for b in binders do
        let label ← b.fvarId!.getUserName
        if label == `fromWriter then return mkAppN visit supplied
        if label == `P then supplied := supplied.push predicate
        else
          let some value := arguments[b.fvarId!]? | throwError "missing the native writer operand {label}"
          supplied := supplied.push value
      throwError "missing the original return continuation"
    let workerType ← whnf (← inferType fromWriter)
    unless workerType.isForall do throwError "expected the original writer continuation"
    withLocalDeclD `readOriginalWriter workerType.bindingDomain! fun source => do
      mkLambdaFVars (inputs.push source) (← mkEqMP recovered (mkApp fromWriter source))

local elab "originalHostVisitType%" : term => do inferType (← originalHostVisit)

/-- A reading on the original writer, its pin substitutions, and its observed delivered
rows gives the reading at the actual submitted field's owner visit. -/
abbrev SignedCalendarAt.OriginalHostVisitStatement : Prop := originalHostVisitType%

/-- Restore the complete submitted route and the original owner memory after reading
the source on its own physical handoff. -/
theorem SignedCalendarAt.frozenHostSourceFromOriginalWriter : SignedCalendarAt.OriginalHostVisitStatement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalHostVisit)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
