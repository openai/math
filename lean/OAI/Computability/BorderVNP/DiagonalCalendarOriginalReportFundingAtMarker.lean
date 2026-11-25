import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportEmissionDomain
import OAI.Computability.BorderVNP.DiagonalOriginalReportPhysicalRead
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldCanonicalEntry
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter

/-! # The physically funded reader on the reported field's original geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyCellReports

set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option cleanup.letToHave false

/-- Select the certificate in the actual calibrated fuel argument, retaining
the checked route supplied by the original raw report family. -/
private def fundedAtOriginalChecks (inputs calibrated : Array Expr) : MetaM Expr := do
  let some oper ← inputs.findM? (fun x => return (← x.fvarId!.getUserName) == `oper)
    | throwError "missing the calibrated original execution"
  let .defnInfo body ← getConstInfo ``SignedCalendarAt.FundedEmissionReadback |
    throwError "expected the original funded readback type"
  let atFuel ← forallBoundedTelescope body.value (some (calibrated.size+1)) fun params _ => do
    let some i ← params.findIdxM? (fun x => return (← x.fvarId!.getUserName) == `funding)
      | throwError "missing the calendar's original funding field"
    return i
  let fuel ← mkProjection oper `funding
  return mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedReturnedOrdinalReadout)
    (calibrated.extract 0 atFuel ++ #[fuel] ++ calibrated.extract atFuel calibrated.size)

private def originalReportRecord (reached : Expr) : MetaM Expr := do
  let mut witness := mkProj ``And 0 reached
  for _ in [0:2] do
    let some ex ← whnfUntil (← inferType witness) ``Exists | throwError "missing the issued bank and data word"
    witness := mkAppN (mkConst ``Classical.choose_spec ex.getAppFn.constLevels!) (ex.getAppArgs.push witness)
  let some ne ← whnfUntil (← inferType witness) ``Nonempty | throwError "missing the actual returned candidate"
  return mkAppN (mkConst ``Classical.choice ne.getAppFn.constLevels!) (ne.getAppArgs.push witness)

private def fundingAtSourceMarker : MetaM Expr :=
  SignedCalendarAt.withCheckedRouteOperands ``SignedCalendarAt.routeInputsOnOriginalReports fun inputs calibrated => do
    let checks := calibrated.back!
    let found := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.reportedCandidateOnOriginalReports) inputs
    let readback := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeReadbackOnOriginalReports) inputs
    let selection ← SignedCalendarAt.certifyOnCheckedCalendar ``SignedCalendarAt.canonicalEntryOnOriginalSelection inputs calibrated
    let writer ← nativeWriterOnCheckedRoutes checks
    let paid ← fundedAtOriginalChecks inputs calibrated
    let outcome := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.OriginalReportEmissionRows) inputs
    forallBoundedTelescope outcome (some 5) fun issued _ => do
      let #[f, u, fit, cells, e] := issued | throwError "expected the original funded field, team, and emission"
      let attained := mkApp found f
      let record ← originalReportRecord attained
      let visit := mkProj ``And 1 attained
      let selected ← SignedCalendarAt.selectIssuedSite readback selection f
      let words := mkProj ``And 1 (mkProj ``And 1 (mkApp writer f))
      withLetDecl `actualOriginalReturn (← inferType record) record fun actual => do
        let value ← withLetDecl `originalFunding (← inferType paid) paid fun funded => do
          let result ← TermElabM.run' do
            let C ← exprToSyntax actual
            let atVisit ← exprToSyntax visit
            let team ← exprToSyntax u
            let receipt ← withoutErrToSorry <| elabTerm (← `(preparedOnAttainedOwner% $C $atVisit $team)) none
            synthesizeSyntheticMVarsNoPostponing
            let (seed, allocation) ← attainedOriginalReportOperands (← instantiateMVars receipt)
            let some allocated ← whnfUntil (← inferType allocation) ``ReportAllocation |
              throwError "expected the actual report bank"
            let some recType ← whnfUntil (← inferType actual) ``ReturnedCandidateReports |
              throwError "expected the registered returned candidate"
            let recInfo ← getConstInfo recType.getAppFn.constName!
            let sites ← forallBoundedTelescope recInfo.type (some recType.getAppNumArgs) fun bs _ => do
              let some i ← bs.findIdxM? (fun b => return (← b.fvarId!.getUserName) == `site)
                | throwError "missing its original site family"
              return recType.getAppArgs[i]!
            let ram ← mkAppM ``readings #[← mkProjection (mkApp sites u) `geometry]
            let atMarker := mkAppN funded #[f, u, allocated.getAppArgs[2]!, ram]
            let next ← whnf (← inferType atMarker)
            unless next.isForall && next.bindingName! == `marked do throwError "lost the original marker operand"
            withLocalDeclD `reportedMarker next.bindingDomain! fun marked => do
              let observed ← physicalReadOnOriginalReport funded f u actual visit selected words seed allocation marked fit cells e
              mkLambdaFVars #[marked] observed
          mkLambdaFVars #[funded] result (generalizeNondepLet := false)
        let original ← mkLambdaFVars #[actual] value (generalizeNondepLet := false)
        mkLambdaFVars issued original (generalizeNondepLet := false)

open Lean Elab Command in
run_cmd liftTermElabM do
  let source ← getConstInfo ``SignedCalendarAt.routeInputsOnOriginalReports
  let value := ShareCommon.shareCommon (← instantiateMVars (← fundingAtSourceMarker))
  if value.hasMVar || value.hasFVar || value.hasSorry then
    throwError "the funded read has an unresolved original field or emission"
  let target := ShareCommon.shareCommon (← instantiateMVars (← inferType value))
  unless ← isProp target do throwError "expected the funded read at the original geometry marker"
  let statement := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.OriginalMarkerFundingStatement
  let result := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.fundedReadAtOriginalReportMarker
  let levels := source.levelParams
  addDecl (.defnDecl {
    name := statement
    levelParams := levels
    type := .sort .zero
    value := target
    hints := .abbrev
    safety := .safe
  })
  addDocStringCore statement "The native funded read of every emitted field, indexed by its returned geometry marker."
  addDecl (.thmDecl {
    name := result
    levelParams := levels
    type := Lean.mkConst statement (levels.map mkLevelParam)
    value := value
  })
  addDocStringCore result "The funded read at the original returned marker, with its native cell bank and observed cell owners."
  let some (.thmInfo _) := (← getEnv).toKernelEnv.find? result |
    throwError "missing the original funded read in the checked environment"

end Diagonal

end BorderVNP
end Computability
end OAI
