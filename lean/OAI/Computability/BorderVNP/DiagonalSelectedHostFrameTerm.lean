import OAI.Computability.BorderVNP.DiagonalSelectedHostFrame
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalReplayCandidateBanks
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations

/-! # Reading the host frame types and returns at the issued inventory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term
open private reachedLookupProjection from OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-- The type of an independently selected frame on a legal routing of the same header. -/
elab "originalHostFrameAt% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.FrameAt

/-- The true candidates on that routing, at the original frame's inventory and site evidence. -/
elab "originalHostSitesAt% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.SitesAt

/-- The original field and cable enumerations of this particular selection. -/
elab "originalHostInventories% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.issuedEnumerations

/-- The chosen candidate with its public operands indexed by the returned team history. -/
elab "originalOnHistorySites% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.siteOnHistory

/-- The genuine intermediate memory and register equalities of those reindexed candidates. -/
elab "originalOnHistoryStages% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.siteOnHistory_stages

end TeamContraction

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- Use the registered processor fields and finite enumeration when reading the site's return predicate. -/
elab "originalHostReturn% " source:term:max : term => do
  let site ← elabTerm source none
  let some native ← whnfUntil (← inferType site) ``CandidateSite | throwError "expected the issued candidate site"
  return mkAppN (mkConst ``CandidateSite.OnReturn native.getAppFn.constLevels!) (native.getAppArgs.push site)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
