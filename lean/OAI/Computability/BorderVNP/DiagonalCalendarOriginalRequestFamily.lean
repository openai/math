import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedNominalPost

/-! # The paid requests of the original reported route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

/-- Use the route returned by this lookup and the price of this execution to
read the precise family of field and team requests from the clock theorem. -/
private def requestsFromReportedRoute : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs native => do
    let some slot ← inputs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `oper)
      | throwError "expected the operative signed execution"
    let rate ← mkProjection inputs[slot]! `post
    let original := native.pop ++ #[rate, native.back!]
    let clock := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.allIssuedPostsOfRequests) original
    let .forallE _ paid _ _ ← whnf (← inferType clock)
      | throwError "expected the paid requests for the returned route"
    return paid

local elab "paidOriginalReportRequests%" : term => requestsFromReportedRoute

/-- Every actual issued field and team pays its source request on the calendar
obtained from these earlier lookup reports. -/
noncomputable abbrev SignedCalendarAt.PaidRequestsOnOriginalReports := paidOriginalReportRequests%

end Diagonal

end BorderVNP
end Computability
end OAI
