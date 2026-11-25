import OAI.Computability.BorderVNP.DiagonalCalendarPlannerSourceData
import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerPostAtSource
import OAI.Computability.BorderVNP.DiagonalIssuedHeaderAtRoster

/-! # Physical post requests on the original issued calendar fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

set_option maxRecDepth 9000
set_option maxHeartbeats 1600000

private def rosterField (application : Expr) (field : Name) : MetaM Expr := do
  let some family := application.getAppFn.constName? | throwError "expected the route's named type"
  let mut type := (← getConstInfo family).type
  for value in application.getAppArgs do
    if type.bindingName! == field then return value
    type := type.bindingBody!.instantiate1 value
  throwError "missing route field {field}"

/-- Apply the planner layout reindexing to its own roster in the installed calendar.
Its five source arguments include the real positive exterior, joint prefix, team
number, native fields and their actual header reading. -/
private def plannerOnOriginalRoute : MetaM Expr := do
  let .defnInfo issuing ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected calendar's issuing routes"
  forallTelescope issuing.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the original native roster"
    let some i ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the source tables"
    let static := parameters.extract 0 i
    let original := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let writer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPlannerPostAt) static
    let rateType ← whnf (← inferType writer)
    unless rateType.isForall && rateType.bindingName! == `rate do
      throwError "expected the physical post rate after the fixed site arguments"
    withLocalDeclD `rate rateType.bindingDomain! fun rate => do
      let pin ← rosterField roster `pin
      let supplied := mkApp2 writer rate pin
      let dataFamily ← mkConstWithLevelParams ``SignedCalendarAt.PlannerSourceData
      let payload := mkAppN dataFamily (static ++ #[rate,pin])
      let transport ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.collectOnRouteHeaders
      let term := mkAppN transport (roster.getAppArgs ++ #[original,payload,supplied])
      let args := parameters.pop ++ #[rate,parameters.back!]
      mkLambdaFVars args term

local elab "plannerPostFamily%" : term => do inferType (← plannerOnOriginalRoute)

/-- The native post requests at the selected exterior, all-team prefix and team
of every issued calendar field. -/
noncomputable abbrev SignedCalendarAt.PlannerPostRequests : Type _ := plannerPostFamily%

/-- On the original field and team, the planner request records the true public
header bits, the transfer of its charge to the deployed request, and its budget. -/
noncomputable def SignedCalendarAt.issuedPlannerPostOperands : SignedCalendarAt.PlannerPostRequests := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← plannerOnOriginalRoute)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
