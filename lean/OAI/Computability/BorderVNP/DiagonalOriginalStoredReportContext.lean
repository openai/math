import OAI.Computability.BorderVNP.DiagonalCalendarCheckedOperation
import OAI.Computability.BorderVNP.DiagonalCalendarFundedPayloadMarks
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportOperation
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredSiteOperator
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The original funded report at the field and team of its payer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta

/-- Operands shared by the coordinate and mark proofs for an original report.
`payerType` is the type of the actual paying operation after its report argument. -/
structure StoredReportPoint where
  /-- Calendar operands with the original field decoder and its route checks. -/
  route : Array Expr
  /-- The calibration arguments through the charged chart. -/
  chart : Array Expr
  /-- The table arguments followed by the actual field's history. -/
  history : Array Expr
  /-- The issued field on the original route. -/
  field : Expr
  /-- The team returning this report. -/
  team : Expr
  /-- The emitted report with the payer's native schema and directory size. -/
  report : Expr
  /-- The remaining obligations of the selected payer after it receives the report. -/
  payerType : Expr
  /-- The retained-payload mark theorem specialized to this history. -/
  markBounds : Expr
  /-- The type of the bank recording the payload's marks. -/
  bankType : Expr

private def throughInput (inputs values : Array Expr) (key : Name) : MetaM (Array Expr) := do
  let some i ← inputs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == key) |
    throwError "the original calendar is missing its {key} operand"
  return values.extract 0 (i+1)

/-- Bind the actual field and team of the payer constructed from the original
route checks. Its report uses the directory cardinality of this history's
retained payload, and the port instance from the payer's own telescope. -/
def withStoredReportOnOriginalInputs (build : StoredReportPoint → MetaM Expr) : MetaM Expr :=
  withCheckedRouteOperands ``routeInputsOnOriginalReports fun inputs route => do
    let some oper ← inputs.findM? (fun x => return (← x.fvarId!.getDecl).userName == `oper) |
      throwError "the original calendar has no operative execution"
    let chargeInputs := route.pop ++ #[← mkProjection oper `post, route.back!]
    let payer := mkAppN (← mkConstWithLevelParams ``chargeReportOnOriginal) chargeInputs
    let (chart, tables) ← forallTelescope (← getConstInfo ``FrozenRouteChecks).type fun fields _ => do
      return (← throughInput fields route `chargeFit, ← throughInput fields route `values)
    withLocalDeclD `f (← nextIssuedInput payer) fun field => do
      withLocalDeclD `u (← nextIssuedInput (mkApp payer field)) fun team => do
        let history := tables.push (mkProj ``Sigma 0 (mkProj ``Sigma 1 field))
        let marks := mkAppN (← mkConstWithLevelParams ``frozenFundedReportMarksOfPayload) history
        let .forallE bank bankType _ _ ← whnf (← inferType marks) |
          throwError "the original payload is missing its bank"
        unless bank.eraseMacroScopes == `bank do throwError "expected the retained report bank"
        let .forallE _ directoryIndex _ _ ← whnf bankType |
          throwError "the original bank has no directory index"
        let some fin ← whnfUntil directoryIndex ``Fin |
          throwError "the original directory does not have a finite index"
        let issued := mkApp2 payer field team
        forallBoundedTelescope (← inferType issued) (some 4) fun schema remaining => do
          let .forallE size _ atSize _ ← whnf remaining | throwError "expected the report cardinality"
          unless size.eraseMacroScopes == `J do throwError "expected the original report's directory size"
          let .forallE name reportType body info ← whnf (atSize.instantiate1 fin.getAppArgs.back!) |
            throwError "the payer has no original report"
          withLocalDecl name info reportType fun report => do
            let point : StoredReportPoint := {
              route := route
              chart := chart
              history := history
              field := field
              team := team
              report := report
              payerType := body.instantiate1 report
              markBounds := marks
              bankType := bankType }
            mkLambdaFVars (#[field,team] ++ schema.push report) (← build point)

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
