import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSelectionWriter
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The published writer selected by the earlier lookup reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

/-- Attach a native operation on a returned site to the actual site recovered
by the earlier lookup for that issued field. -/
def SignedCalendarAt.onEarlierReportedSite (operation : Name) : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs original => do
    let billed ← SignedCalendarAt.certifyOnCheckedCalendar operation inputs original
    let actual := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput billed) fun f => do
      let chosen ← SignedCalendarAt.selectIssuedSite actual billed f
      mkLambdaFVars #[f] (mkApp2 billed f chosen)

private def earlierWriter := SignedCalendarAt.onEarlierReportedSite
  ``SignedCalendarAt.publishedWriterOnOriginalSelectionOfCandidates

local elab "writerOnEarlierReportedSite%" : term => do inferType (← earlierWriter)

/-- The original field and team have a published writer on the replayed site
selected by the given lookup reports. -/
abbrev SignedCalendarAt.PublishedWriterOnEarlierReports : Prop := writerOnEarlierReportedSite%

/-- Read this writer from the received lookup and the actual replay of the
field's assignment. -/
theorem SignedCalendarAt.publishedWriterAtEarlierReports : SignedCalendarAt.PublishedWriterOnEarlierReports := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← earlierWriter)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
