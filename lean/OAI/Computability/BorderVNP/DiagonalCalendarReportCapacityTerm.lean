import OAI.Computability.BorderVNP.DiagonalCalendarSiteReportCapacity

/-! # Applying the calendar’s physical capacity bounds to an issued report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term in
/-- Apply the word and allocation bounds to the site and frame already carried
by the selected report test, including its original inventory instance. -/
elab "calendarSiteReportCapacity%" provider:term:max raw:term:max : term <= goal => do
  let provider ← elabTerm provider none
  let raw ← elabTerm raw none
  let some target ← whnfUntil goal ``SignedCalendarAt.frozenReportTest
    | throwError "expected the selected report test"
  let all := target.getAppArgs
  forallTelescope (← whnf (← inferType provider)) fun binders _ => do
    let names ← binders.mapM (fun b => b.fvarId!.getUserName)
    unless names[0]? == some `values && names.back? == some `frame do
      throwError "expected the complete site-capacity quantifiers: {names}"
    unless all.size > binders.size do throwError "expected all arguments to the report test"
    let tail := all.extract (all.size - (binders.size + 1)) (all.size - 1)
    let some rawPos := names.idxOf? `raw | throwError "missing the checked broadcast"
    let some index := names.idxOf? `I | throwError "missing the site inventory"
    let known := mkAppN (Lean.mkConst ``SignedCalendarAt.frozenSiteReportCapacity [← getDecLevel tail[index]!])
      provider.getAppArgs
    return mkAppN known (tail.set! rawPos raw)

end Diagonal

end BorderVNP
end Computability
end OAI
