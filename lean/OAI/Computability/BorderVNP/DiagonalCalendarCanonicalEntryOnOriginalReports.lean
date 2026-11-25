import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldCanonicalEntry
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The original canonical directory from the returned report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option cleanup.letToHave false
set_option maxRecDepth 22000
set_option maxHeartbeats 16000000

private def entriesOnOriginalReports : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs calibrated => do
    let entries ← SignedCalendarAt.certifyOnCheckedCalendar
      ``SignedCalendarAt.canonicalEntryOnOriginalSelection inputs calibrated
    let readback := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    withLocalDeclD `f (← SignedCalendarAt.nextIssuedInput entries) fun f => do
      let site ← SignedCalendarAt.selectIssuedSite readback entries f
      mkLambdaFVars #[f] (mkApp2 entries f site)

local elab "entriesOnOriginalReports%" : term => entriesOnOriginalReports

private noncomputable def originalEntries : PSigma fun claim : Prop => claim :=
  ⟨_, entriesOnOriginalReports%⟩

/-- For every field and team of the original returned report family, the selected site's
native program publishes the canonical directory. Its slotted writer and report conversion
use the same middle memory and the public bank of the issuing processor. -/
theorem SignedCalendarAt.canonicalEntryOnOriginalReports : originalEntries.1 := originalEntries.2

end Diagonal

end BorderVNP
end Computability
end OAI
