import OAI.Computability.BorderVNP.DiagonalSelectedLookupWriterLabel

/-! # The selected site's physical return and its recorded stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term

-- Each projection has exactly the parameters of the selected frame before the
-- frame itself. Reusing its arguments avoids inferring its wire layout again.
private def reachedLookupProjection (source : Syntax) (project : Name) : TermElabM Expr := do
  let selected ← elabTerm source none
  let some native ← whnfUntil (← inferType selected) ``PreparationFrame.SelectedLookupSites |
    throwError "expected the selected original lookup sites"
  let .const _ levels := native.getAppFn | throwError "expected a native lookup application"
  return mkAppN (mkConst project levels) (native.getAppArgs.push selected)

/-- The physical site for a returned exterior and team in the supplied lookup frame. -/
elab (name := originalLookupSites) "originalLookupSites% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.returnedSite

/-- The recorded stage evidence for the same returned exterior and team. -/
elab (name := originalLookupStages) "originalLookupStages% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.returnedSiteStages

/-- The original per-site evidence on the installed frame's own exterior. -/
elab (name := originalLookupAttained) "originalLookupAttained% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.attained

/-- The writer's label with the original site's inventory and wire parameters. -/
elab (name := writerLabelOfSelected) "writerLabelOfSelected% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.writerLabel

end TeamContraction

end BorderVNP
end Computability
end OAI
