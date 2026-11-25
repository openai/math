import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldReportWords
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The original report family at the enrolled native site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 16000000

private def wordsFromOriginalReports : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs calibrated => do
    let certificate ← SignedCalendarAt.certifyOnCheckedCalendar
      ``SignedCalendarAt.reportWordsOnOriginalSelection inputs calibrated
    let readback := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput certificate) fun f => do
      let selected ← SignedCalendarAt.selectIssuedSite readback certificate f
      mkLambdaFVars #[f] (mkApp2 certificate f selected)

local elab "reportWordsFromOriginalReports%" : term => wordsFromOriginalReports

private noncomputable def originalReports : PSigma fun claim : Prop => claim :=
  ⟨_, reportWordsFromOriginalReports%⟩

/-- For every original field and team, its native slotted writer and signed
report words come from the same site selected by the supplied report family. -/
theorem SignedCalendarAt.reportWordsOnOriginalReports : originalReports.1 := originalReports.2

end Diagonal

end BorderVNP
end Computability
end OAI
