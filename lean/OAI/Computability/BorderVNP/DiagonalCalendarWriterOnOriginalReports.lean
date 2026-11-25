import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldWriter
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The issued writers of an original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 16000000

private def writerAtReportedSites : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs calibrated => do
    let certificate ← SignedCalendarAt.certifyOnCheckedCalendar
      ``SignedCalendarAt.writerOnOriginalSelection inputs calibrated
    let readback := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput certificate) fun f => do
      let selected ← SignedCalendarAt.selectIssuedSite readback certificate f
      mkLambdaFVars #[f] (mkApp2 certificate f selected)

local elab "originalReportWriter%" : term => writerAtReportedSites

private noncomputable def writersOnReports : PSigma fun claim : Prop => claim :=
  ⟨_, originalReportWriter%⟩

/-- For each original report family the issued field determines a site on its
admitted frame. The native writer uses the site's placement arrays and the
original team's owned return retains its published RAM. -/
theorem SignedCalendarAt.writerOnOriginalReports : writersOnReports.1 := writersOnReports.2

end Diagonal

end BorderVNP
end Computability
end OAI
