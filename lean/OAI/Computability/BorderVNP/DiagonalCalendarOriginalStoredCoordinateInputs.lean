import OAI.Computability.BorderVNP.DiagonalOriginalStoredReportContext
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerReportCoordinates

/-! # The four coordinates of a stored report on the original inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.Evaluator

private theorem savedCoordinates {A B C W : Type*}
    (a : A) (b : B) (c : C) (w : W) (originalDecl : A)
    {packetLabel plannedLabel : B} {receiver plannedReceiver : C} {width plannedWidth : W}
    (registered : packetLabel = plannedLabel ∧ receiver = plannedReceiver ∧ width = plannedWidth)
    (declaration : a = originalDecl) (label : b = packetLabel) (recv : c = receiver)
    (incoming : w = width) :
    (a, b, c, w) = (originalDecl, plannedLabel, plannedReceiver, plannedWidth) :=
  Prod.ext declaration <| Prod.ext (label.trans registered.1) <|
    Prod.ext (recv.trans registered.2.1) (incoming.trans registered.2.2)

/-- Decode the actual route of this field, with the grid's own owner function. -/
private def recordedDeclaration (point : SignedCalendarAt.StoredReportPoint) : MetaM Expr := do
  let planner := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPlannerTask) point.chart
  let cube ← mkProjection planner `cube
  let routing := mkProj ``Subtype 0 (mkProj ``Sigma 0 (mkProj ``Sigma 1 (mkProj ``Sigma 1 point.field)))
  let some routed ← whnfUntil (← inferType routing) ``Cube.Physical.NativeAssignments.Routed
    | throwError "expected the original field's routed assignment"
  let owners := routed.getAppArgs.back!
  let published ← mkAppM ``SignedPrep.routeBroadcast #[cube, owners, routing]
  return mkApp2 (← mkConstWithLevelParams ``SignedPrep.decodedBroadcast) cube (mkProj ``Subtype 0 published)

private def coordinateInputs (point : SignedCalendarAt.StoredReportPoint) : MetaM Expr := do
  let .forallE name target _ _ ← whnf point.payerType | throwError "expected the report coordinates"
  unless name.eraseMacroScopes == `coordinates do throwError "expected the coordinate input of the payer"
  let registered := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPlannerReportCoordinates) point.history
  let fields ← #[`declaration, `label, `recv, `incoming].mapM (mkProjection point.report)
  let proof ← mkAppM ``savedCoordinates (fields ++ #[← recordedDeclaration point, registered])
  forallBoundedTelescope (← inferType proof) (some 4) fun saved _ => do
    mkLambdaFVars saved (mkExpectedPropHint (mkAppN proof saved) target)

set_option maxRecDepth 20000
set_option maxHeartbeats 7400000
set_option cleanup.letToHave false

open Lean.Elab.Term in
local elab "originalStoredCoordinates%" : term => SignedCalendarAt.withStoredReportOnOriginalInputs coordinateInputs

private def coordinateStatement {P : Prop} (h : P) : PSigma fun p : Prop => p := ⟨P, h⟩

private noncomputable def originalStoredCoordinates : PSigma fun p : Prop => p :=
  coordinateStatement originalStoredCoordinates%

/-- For every field and team on the original report inputs, the four saved equalities
give the payer its declaration, packet label, receiving cell and incoming row width. -/
theorem SignedCalendarAt.paidCoordinatesAtOriginalInputs : originalStoredCoordinates.1 :=
  originalStoredCoordinates.2

end Diagonal

end BorderVNP
end Computability
end OAI
