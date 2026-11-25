import OAI.Computability.BorderVNP.DiagonalRecordedGeometryTerm
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback

/-! # The physical publication at a selected exterior and team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term PackedHistoryCircuit TeamContraction
open RoutingISA.Evaluator.SignedPrep

private def selectedStage (selectedType value x team : Expr) (field : Name) : Expr :=
  mkAppN (mkConst field selectedType.getAppFn.constLevels!)
    ((selectedType.getAppArgs.push value) ++ #[x,team])

private def slottedReturn (pin site : Expr) : TermElabM Expr := do
  let some native ← whnfUntil (← inferType pin) ``PublishedPin | throwError "expected the observed physical pin"
  let some receipt ← whnfUntil (← inferType site) ``CandidateSite | throwError "expected the selected original site"
  let get (name : Name) := mkAppN (mkConst name receipt.getAppFn.constLevels!) (receipt.getAppArgs.push site)
  return mkAppN (mkConst ``PublishedPin.actual_slotted native.getAppFn.constLevels!)
    (native.getAppArgs ++ #[pin, get ``CandidateSite.epoch, get ``CandidateSite.published])

/-- Read the capacity of the private layout, the routing header, the stored packet and the
published pin at a specified exterior and team. All four refer to the site's own native
geometry and the two returns of its epoch and directory programs. -/
elab (name := nativeHostPublicationAt) "nativeHostPublicationAt% " planner:term:max routing:term:max values:term:max hist:term:max
    selected:term:max exterior:term:max team:term:max : term => do
  let op ← elabTerm planner none
  let some fixed ← whnfUntil op ``SignedCalendarAt.frozenPlannerTask | throwError "expected the original planner task"
  let parameters ← fixed.getAppArgs.mapM exprToSyntax
  let task ← `(@SignedCalendarAt.frozenPlannerTask $parameters*)
  let original ← elabTerm selected none
  let some info ← whnfUntil (← inferType original) ``PreparationFrame.SelectedLookupSites |
    throwError "expected the chosen original returned sites"
  let x ← elabTerm exterior none
  let u ← elabTerm team none
  let reached := selectedStage info original x u ``PreparationFrame.SelectedLookupSites.returnedSiteStages
  let site := selectedStage info original x u ``PreparationFrame.SelectedLookupSites.returnedSite
  let found := mkProj ``And 0 reached
  let some returned ← whnfUntil (← inferType found) ``Exists | throwError "expected the return of the chosen team"
  let result := mkAppN (mkConst ``Exists.choose_spec returned.getAppFn.constLevels!) (returned.getAppArgs.push found)
  withLetDecl `observedSite (← inferType result) result fun result => do
    let on ← exprToSyntax (mkProj ``And 0 result)
    let hardware := mkProj ``And 1 (mkProj ``And 1 (mkProj ``And 1 result))
    let boot ← exprToSyntax (mkProj ``And 0 hardware)
    let issued := mkProj ``And 1 hardware
    let pin ← exprToSyntax (mkProj ``And 0 issued)
    let packet ← exprToSyntax (mkProj ``And 0 (mkProj ``And 1 issued))
    let geometry ← elabTerm (← `(geometryFromNative% $task $routing $values $hist $team $boot $pin $packet $on)) none
    let data := mkProj ``PLift 0 geometry
    withLetDecl `registeredPhysical (← inferType data) data fun physical => do
      let actual ← slottedReturn (mkProj ``And 1 (mkProj ``And 1 physical)) site
      let fits := mkProj ``And 0 (mkProj ``And 1 actual)
      let paired := mkAppN (mkConst ``And.intro) #[← inferType fits,← inferType physical,fits,physical]
      let body ← mkLetFVars #[physical] paired
      mkLetFVars #[result] body

end Diagonal

end BorderVNP
end Computability
end OAI
