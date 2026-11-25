import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalOwnerBaseAtRoutes

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

/-- Apply the observed owner-table operation to the calibrated route, using the
core, source roster, and task address appearing in the type of that very route. -/
private def ownerTablesOnSelectedRoutes : MetaM Expr := do
  let .defnInfo routeType ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calibrated family of issuing routes"
  forallTelescope routeType.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected a route over the selected native source roster"
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let owners ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.ownerBaseAtRoutes
    mkLambdaFVars parameters (mkAppN owners (roster.getAppArgs.push routed))

local elab "selectedOwnerTableType%" : term => do inferType (← ownerTablesOnSelectedRoutes)

/-- The selected calendar parameters, followed by the native acquisition and
calls on which the physical source reports were issued. -/
noncomputable abbrev SignedCalendarAt.FrozenOwnerTableOperation : Type _ := selectedOwnerTableType%

/-- The base and owner table of the supported column on every prepared positive
tuple. The base is the pre-call limit. The owner words come from the same native
input on which the selected calls were run. -/
noncomputable def SignedCalendarAt.frozenBaseOwnerOfCandidates :
    SignedCalendarAt.FrozenOwnerTableOperation := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← ownerTablesOnSelectedRoutes)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
