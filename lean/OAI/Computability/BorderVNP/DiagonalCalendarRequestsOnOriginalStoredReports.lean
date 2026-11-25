import OAI.Computability.BorderVNP.DiagonalCalendarChargeOnOriginalStoredReport
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalRequestFamily
import OAI.Computability.BorderVNP.DiagonalCalendarStoredOriginalReportFamily

/-! # The actual paid requests of a single original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.FragmentRows

set_option cleanup.letToHave false
set_option maxRecDepth 22000
set_option maxHeartbeats 14000000

/-- Recognize the original box-width assumption if it occurs in the store
telescope. The paid requests on already returned reports need no such input. -/
private def originalHeaderWidth (header field : Expr) : MetaM Bool := do
  let type ← inferType field
  unless type.isAppOfArity ``Fact 1 do return false
  let bound := type.getAppArgs.back!
  unless bound.isAppOfArity ``LE.le 4 do return false
  let args := bound.getAppArgs
  return (← whnf args[2]!).rawNatLit? == some 8 && args[3]! == header

/-- Work over the actual store domain used by the native site theorem.
The second parameter list belongs to its earlier lookup. -/
private def withOriginalStoredReports (body : Array Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let family ← mkConstWithLevelParams ``SignedCalendarAt.StoredReportsAtOriginalInputs
  forallTelescope (← inferType family) fun parameters _ => do
    let some header ← parameters.findM? (fun x=>return (← x.fvarId!.getDecl).userName == `header)
      | throwError "expected the original calendar header"
    let lookup ← parameters.filterM (fun x => return !(← originalHeaderWidth header x))
    withLocalDeclD `stored (mkAppN family parameters) (body parameters lookup)

private def originalStoredRequestType : MetaM Expr :=
  withOriginalStoredReports fun parameters lookup reports => do
    let paid ← mkConstWithLevelParams ``SignedCalendarAt.PaidRequestsOnOriginalReports
    mkForallFVars (parameters.push reports) (mkAppN paid lookup)

private def originalStoredRequestProof : MetaM Expr :=
  withOriginalStoredReports fun parameters lookup reports => do
    withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput reports) fun f => do
      withLocalDeclD `u (← SignedCalendarAt.nextIssuedInput (mkApp reports f)) fun u => do
        let row ← SignedCalendarAt.storedReportAtOriginalSite (mkApp2 reports f u)
        let some facts ← whnfUntil (← inferType (mkProj ``Subtype 1 row)) ``EmittedReport.FundedFacts
          | throwError "expected the thirteen facts stored with an original report"
        let charge := mkConst ``SignedCalendarAt.chargeOnOriginalStoredReport facts.getAppFn.constLevels!
        let paid ← SignedCalendarAt.payStoredOriginalReport (mkAppN charge (lookup ++ #[f,u])) row
        mkLambdaFVars (parameters ++ #[reports,f,u]) paid

local elab "requestsOfOriginalStoredFamily%" : term => originalStoredRequestType

/-- The literal earlier-route request family, with one native report store as its input. -/
abbrev SignedCalendarAt.RequestsFromOriginalStoredFamily : Prop := requestsOfOriginalStoredFamily%

/-- The family used for the original native calls pays the request of each
issued field and team on the earlier reported route. -/
theorem SignedCalendarAt.requestsOnOriginalStoredReports : SignedCalendarAt.RequestsFromOriginalStoredFamily := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalStoredRequestProof)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
