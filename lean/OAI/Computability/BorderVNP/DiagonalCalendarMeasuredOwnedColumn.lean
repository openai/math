import OAI.Computability.BorderVNP.DiagonalCalendarMeasuredPreparedColumn
import OAI.Computability.BorderVNP.DiagonalCalendarFundedOwnerPair
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedAtRoutes

/-! # The actual owner on the packet of the measured calendar column -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

set_option maxRecDepth 14000
set_option maxHeartbeats 7200000

private def declaredParameter (type : Expr) (wanted : Name) : MetaM Nat :=
  forallTelescope type fun xs _ => do
    let some i ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == wanted)
      | throwError "missing original calendar parameter {wanted}"
    return i

/-- The route and source of the measured preparation determine the installed
native call. Its actual owner table is the fourth input at that preparation. -/
private def measuredFundedOwner : MetaM Expr := do
  let .defnInfo prepared ← getConstInfo ``SignedCalendarAt.measuredPreparedColumn
    | throwError "expected the measured original calendar"
  lambdaTelescope prepared.value fun front _ => do
    let valid := front.back!
    forallTelescope (← inferType valid) fun _ result => do
      let some route ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks
        | throwError "expected the original field route check"
      let args := route.getAppArgs
      let calibrated := (args.extract 0 (args.size-3)).push valid
      let run := mkAppN (← mkConstWithLevelParams prepared.name) front
      let supply := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSuppliedAtRoutes) calibrated
      let selected := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) calibrated
      let some roster ← whnfUntil (← inferType selected) ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
        | throwError "expected the original calendar's native roster"
      let pinAt ← declaredParameter (← getConstInfo ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes).type `pin
      let pin := roster.getAppArgs[pinAt]!
      let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
        | throwError "expected the original route operands"
      let valuesAt ← declaredParameter shape.value `values
      let callPrefix := (calibrated.extract 0 valuesAt).push pin
      let clock ← whnf (← inferType run)
      let inputs ← whnf (← inferType supply)
      withLocalDecl `measured clock.binderInfo clock.bindingDomain! fun measured => do
        withLocalDecl `funded inputs.binderInfo inputs.bindingDomain! fun funded => do
          let source := mkProj ``Prod 1 (mkApp supply funded)
          let calls := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenNativeCalls)
            (callPrefix ++ #[measured,source])
          let owner := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenBaseOwnerOfFundedCandidates)
            (calibrated ++ #[funded,calls])
          let returned := mkAppN run #[measured,source,mkProj ``Subtype 1 owner]
          mkLambdaFVars (front ++ #[measured,funded]) returned

local elab "measuredFundedOwnerType%" : term => do inferType (← measuredFundedOwner)

/-- The operation remaining after the measured calendar takes the real
owner table from the supplied native packet. -/
noncomputable abbrev SignedCalendarAt.MeasuredFundedOwnerResult : Type _ := measuredFundedOwnerType%

/-- Continue the measured calendar column with the owner table of the calls
run on its funded packet. The remaining inputs are the issued private rows
and their guarded completion. -/
noncomputable def SignedCalendarAt.measuredOwnedColumn : SignedCalendarAt.MeasuredFundedOwnerResult := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← measuredFundedOwner)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
