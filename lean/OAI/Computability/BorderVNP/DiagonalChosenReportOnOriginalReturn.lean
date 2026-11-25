import OAI.Computability.BorderVNP.DiagonalCandidateAfterOwned

/-! # Selecting the report at an original ownership return

The report family supplies a bank, a family of digits and a returned report at the same
screened declaration. Preserve the given native history and all of its handoff witnesses
when selecting those data. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.OriginalReportReturn

open Lean Meta Elab Term RoutingISA.Evaluator.SignedPrep

private def chosenFacts (proof : Expr) : MetaM Expr := do
  let some witness ← whnfUntil (← inferType proof) ``Exists
    | throwError "expected an existential in the returned report"
  let chosen := Lean.mkConst ``Classical.choose_spec witness.getAppFn.constLevels!
  return mkAppN chosen (witness.getAppArgs.push proof)

/-- Select one report from the reached report family at exactly the given native return.
The bank and the report digits are the nested witnesses of that same application. -/
elab "chosenReportOnOriginalReturn%" earned:term:max words:term:max history:term:max
    delivery:term:max table:term:max row:term:max writer:term:max runs:term:max
    pins:term:max received:term:max matched:term:max returned:term:max
    handoff:term:max observed:term:max : term => do
  let family ← elabTerm earned none
  let arguments ← #[words, history, delivery, table, row, writer, runs, pins, received,
    matched, returned, handoff, observed].mapM fun stx => elabTerm stx none
  let afterBank ← chosenFacts (mkAppN family arguments)
  let afterDigits ← chosenFacts afterBank
  let some nonempty ← whnfUntil (← inferType afterDigits) ``Nonempty
    | throwError "the original bank and digits did not yield a report"
  unless (← whnfUntil nonempty.getAppArgs[0]! ``ReturnedCandidateReports).isSome do
    throwError "expected the signed report on the given ownership return"
  let choose := Lean.mkConst ``Classical.choice nonempty.getAppFn.constLevels!
  return mkAppN choose (nonempty.getAppArgs.push afterDigits)

end Diagonal.OriginalReportReturn

end BorderVNP
end Computability
end OAI
