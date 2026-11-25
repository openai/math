import OAI.Computability.BorderVNP.DiagonalCalendarWriterPostChosenClock
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # The chosen signed clock from native writer requests on the original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

set_option maxRecDepth 26000
set_option maxHeartbeats 25600000
set_option cleanup.letToHave false

/-- Instantiate the leading binders in the stored native family in a single substitution.
This preserves its actual request domain, including the physical route and clock. -/
private def onOriginalOperands (family : Expr) (operands : Array Expr) : MetaM Expr := do
  let mut tail := family
  for _ in operands do
    let .forallE _ _ body _ := tail.consumeMData | return ← instantiateForall family operands
    tail := body
  return tail.instantiateRev operands

/-- Retain the name of the original report family in the public replay operation. -/
private def nameOriginalReplay : Expr → Expr
  | .forallE n t body bi =>
    .forallE (if n.eraseMacroScopes == `reports then `replay else n) t (nameOriginalReplay body) bi
  | e => e

/-- Read the same grid, source tables, pin and entries as the actual report checker.
The final proposition and its proof use the same bound request. -/
private def clockOnOriginalRequests : MetaM (List Name × Expr × Expr) := do
  let route ← getConstInfo ``SignedCalendarAt.routeInputsOnOriginalReports
  let issuance ← mkConstWithLevelParams ``SignedCalendarAt.allIssuedPostsOfRequests
  let clock ← mkConstWithLevelParams ``SignedCalendarAt.frozenChosenClockOfWriterPost
  let .defnInfo native ← getConstInfo ``SignedCalendarAt.NominalIssuedPostMap
    | throwError "expected the native writer's original request family"
  let .defnInfo chosen ← getConstInfo ``SignedCalendarAt.WriterPostChosenClockRequest
    | throwError "expected the chosen clock request at the frozen pin"
  let routeType := nameOriginalReplay route.type
  forallBoundedTelescope routeType (some routeType.getForallArity) fun allInputs result => do
    unless result.isAppOf ``SignedCalendarAt.FrozenRouteChecks do
      throwError "expected the selected calendar's actual route checks"
    let actual := result.getAppArgs
    unless allInputs.size ≥ 3 && actual.size ≥ 6 do throwError "missing the original pin, history or proposal"
    let setup := actual.extract 0 (actual.size - 6)
    let values := actual[actual.size - 6]!
    let h := actual[actual.size - 5]!
    let originalEntries := actual[actual.size - 4]!
    let entries := originalEntries.etaExpandedStrict?.getD originalEntries
    let inputs := allInputs.extract 0 (allInputs.size - 3)
    let some oper ← inputs.findM? (fun x => do
      return (← x.fvarId!.getUserName).eraseMacroScopes == `oper)
      | throwError "missing the frozen execution"
    let checked := mkAppN (← mkConstWithLevelParams route.name) inputs
    let rate ← mkAppM ``FrozenExecutionAt.post #[oper]
    let nativeArgs := setup ++ #[values, h, entries, rate, checked]
    let implication ← onOriginalOperands native.value nativeArgs
    let .forallE _ request _ _ := implication.consumeMData
      | throwError "missing the charge on the native requests"
    let originalClock := (mkAppN chosen.value setup).headBeta
    unless originalClock.isAppOf ``PostInputTarget do throwError "expected the calibrated clock map"
    let target := (mkApp originalClock.getAppArgs.back! h).headBeta
    unless target.isAppOf ``SignedCalendarAt.FrozenClockAtPin do throwError "expected the original clock at the encoded pin"
    withLocalDeclD `requests request fun requests => do
      let post := mkApp (mkAppN issuance nativeArgs) requests
      let atPin := mkAppN clock (setup ++ #[oper, values, h, entries, checked, post])
      let params := inputs.push requests
      return (route.levelParams, ← mkForallFVars params target, ← mkLambdaFVars params atPin)

open Elab.Command in
set_option Elab.async false in
run_cmd liftTermElabM do
  let (levels, statement, proof) ← clockOnOriginalRequests
  let name := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.clockFromOriginalRequests
  addDecl (.thmDecl { name, levelParams := levels, type := statement, value := proof })
  addDocStringCore name "Every native writer request on the original replay supplies the chosen signed clock at its encoded pin."

end Diagonal

end BorderVNP
end Computability
end OAI
