import OAI.Computability.BorderVNP.DiagonalOriginalReportPhysicalRead
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarCanonicalEntryOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarReportWordsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalReturnedEntryPlacement
import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation

/-! # The signed report of each original team at the original canonical directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyCellReports FiniteEvaluator
set_option maxHeartbeats 10000000
set_option maxRecDepth 22000
set_option cleanup.letToHave false

open Lean Meta Elab Term in
/-- Read the original site, layout, cursor and bank from the same attained
control and allocation before transporting the signed words to the canonical directory. -/
local elab "attainedCanonicalReport% " raw:term:max carry:term:max ready:term:max
    place:term:max prepared:term:max allocated:term:max : term => withoutErrToSorry do
  let source ← elabTerm raw none
  let transport ← elabTerm carry none
  let control ← elabTerm ready none
  let placement ← elabTerm place none
  let seed ← elabTerm prepared none
  let allocation ← elabTerm allocated none
  let some opened ← whnfUntil (← inferType control) ``OpenSuffix.Ready |
    throwError "expected the original opened control"
  let some scan ← whnfUntil opened.getAppArgs[0]! ``RoutingISA.SignedTaskArena.Layout.openInputs |
    throwError "expected the physical bundle headers and owners"
  let #[_, _, _, offsets, ctl, live, ports, bundles, bits, homes, headers] := scan.getAppArgs |
    throwError "unexpected original report opening"
  let some input ← whnfUntil (← inferType seed) ``PreparedReportInput |
    throwError "expected the prepared original cells"
  let #[_, layout, _, _, rows, cursor, width] := input.getAppArgs |
    throwError "unexpected prepared report row"
  let some bank ← whnfUntil (← inferType allocation) ``ReportAllocation |
    throwError "expected the allocated original cell bank"
  let native := mkAppN source #[bundles, bits, offsets, ctl, live, ports, homes, headers, control,
    placement, layout, rows, cursor, width, seed, bank.getAppArgs[2]!, allocation]
  let address ← whnf (← inferType native)
  let some eq ← whnfUntil address.bindingDomain! ``Eq | throwError "expected the original bank address"
  let received := mkApp native (← mkEqRefl eq.getAppArgs[1]!)
  let some recorded ← whnfUntil (← inferType received) ``RoutingISA.SignedTaskArena.ReportWords |
    throwError "expected the returned report words"
  let #[_, frame, _, written, output, signed] := recorded.getAppArgs |
    throwError "unexpected original returned word coordinates"
  return mkAppN transport #[frame, written, output, signed, received]

private def reportedWordsAtOriginalCells : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs _ => do
    let found := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.reportedCandidateOnOriginalReports) inputs
    let words := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.reportWordsOnOriginalReports) inputs
    let slots := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.canonicalEntryOnOriginalReports) inputs
    forallBoundedTelescope (← inferType words) (some 2) fun pair _ => do
      let #[f, u] := pair | throwError "expected the original field and its team"
      let observedField := mkApp found f
      let reached := mkProj ``And 0 observedField
      let bank ← mkAppM ``Classical.choose_spec #[reached]
      let digits ← mkAppM ``Classical.choose_spec #[bank]
      let C ← mkAppM ``Classical.choice #[digits]
      let opened ← mkProjection C `opened
      let control := mkApp (mkProj ``And 1 opened) u
      let raw := mkProj ``And 1 (mkAppN words pair)
      let slot := mkAppN slots pair
      let canon := mkProj ``And 1 (mkProj ``And 1 (mkProj ``And 1 slot))
      let result ← TermElabM.run' do
        let entry ← exprToSyntax control
        let ready ← exprToSyntax (← mkProjection control `ready)
        let placed ← withoutErrToSorry <| elabTerm (← `(originalPaidPlacement% $entry)) none
        let candidate ← exprToSyntax C
        let reachedVisit ← exprToSyntax (mkProj ``And 1 observedField)
        let team ← exprToSyntax u
        let receipt ← withoutErrToSorry <| elabTerm (← `(preparedOnAttainedOwner% $candidate $reachedVisit $team)) none
        synthesizeSyntheticMVarsNoPostponing
        let (source, allocation) ← attainedOriginalReportOperands (← instantiateMVars receipt)
        let home ← exprToSyntax source
        let banks ← exprToSyntax allocation
        let observed ← exprToSyntax raw
        let canonical ← exprToSyntax canon
        let position ← exprToSyntax placed
        let returned ← withoutErrToSorry <| elabTerm (← `(attainedCanonicalReport% $observed $canonical $ready $position $home $banks)) none
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars returned
      mkLambdaFVars pair result

local elab "reportedWordsAtOriginalCells%" : term => reportedWordsAtOriginalCells

private noncomputable def issuedCanonicalReturn : PSigma fun claim : Prop => claim :=
  ⟨_, reportedWordsAtOriginalCells%⟩

/-- The signed original sparse report at each field and team, with its
actual original cells and bank written into the canonical directory. -/
theorem SignedCalendarAt.encodedWordsOnOriginalReports : issuedCanonicalReturn.1 :=
  issuedCanonicalReturn.2

end Diagonal

end BorderVNP
end Computability
end OAI
