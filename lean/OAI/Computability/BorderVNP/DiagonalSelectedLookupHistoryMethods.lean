import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalReplayCandidateBanks

/-! # The issued history and its exact tail evidence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term
open private reachedLookupProjection from OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

-- The last argument of each physical observation is the actual returned tail.
-- Capture it under its own team binder before assembling the method application.
private def onActualHistory (name : Name) (chosen exterior history actual : Syntax) : TermElabM Expr := do
  let method ← reachedLookupProjection chosen name
  let x ← elabTerm exterior none
  let h ← elabTerm history none
  let observed ← elabTerm actual none
  let tail ← forallBoundedTelescope (← inferType observed) (some 1) fun teams body => do
    unless teams.size == 1 do throwError "expected one observation per issued team"
    let some first ← whnfUntil body ``And | throwError "expected the recorded public argument"
    let some second ← whnfUntil first.appArg! ``And | throwError "expected the recorded macro library and remaining facts"
    mkLambdaFVars teams second.appArg!
  return mkAppN method #[x,h,tail,observed]

/-- Use the actual returned observation at the input exterior, retaining its last conjunct. -/
elab "originalSiteOnActual% " chosen:term:max exterior:term:max history:term:max actual:term:max : term =>
  onActualHistory ``PreparationFrame.SelectedLookupSites.siteOnHistory chosen exterior history actual

/-- Preserve the chronology on the same returned observation and team. -/
elab "originalStagesOnActual% " chosen:term:max exterior:term:max history:term:max actual:term:max : term =>
  onActualHistory ``PreparationFrame.SelectedLookupSites.siteOnHistory_stages chosen exterior history actual

end TeamContraction

end BorderVNP
end Computability
end OAI
