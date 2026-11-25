import OAI.Computability.BorderVNP.DiagonalCalendarRoutedAt
import OAI.Computability.BorderVNP.DiagonalSelectedBareReportCut

/-! # The assigned native report on the original calendar route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta
open PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

/-- Apply the single-admission report theorem to the very same arguments that define the
calendar's route. This retains its dependent input types, boot programs and admission proof. -/
private def originalPinnedReportProof : MetaM Expr := do
  let .defnInfo route ← getConstInfo ``SignedCalendarAt.frozenRoutedAt
    | throwError "expected the original calendar route definition"
  lambdaTelescope route.value fun inputs body => do
    let some entered ← whnfUntil body ``signedAdmittedRouting
      | throwError "the calendar must enter the signed admitted route"
    let observe ← mkConstWithLevelParams ``signedAdmittedBareReportCut
    mkLambdaFVars inputs (mkAppN observe entered.getAppArgs)

local elab "originalPinnedReportType%" : term => do
  inferType (← originalPinnedReportProof)

/-- The report associated with each admitted field, its original physical route,
and the chosen sequence of cell measurements on that route. -/
abbrev SignedCalendarAt.OriginalPinnedReportObservations : Prop := originalPinnedReportType%

/-- Reading before the original field's private calls recovers its assigned cell reports. -/
theorem SignedCalendarAt.frozenPinnedReportCutAt : SignedCalendarAt.OriginalPinnedReportObservations := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← originalPinnedReportProof)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
