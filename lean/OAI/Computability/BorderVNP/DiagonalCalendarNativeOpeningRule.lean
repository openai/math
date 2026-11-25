import OAI.Computability.BorderVNP.DiagonalCanonicalCandidateReplay
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests

/-! # The native report-opening rule on a returned calendar lookup

The selected lookup fixes the physical writer, the shared frame and both finite
enumerations. The report test fixes every calendar operand of the opening rule.
Together they specialize it to one premise on the actual return history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction

private def openingHead (e : Expr) (n : Name) : MetaM Expr := do
  let some h ← whnfUntil e n | throwError "expected {n} in the current opening certificate"
  return h

/-- Recover the operands from the same reported test and the original checked
writer. The result is precisely the existing opening theorem on those two
records, awaiting its one native handler. -/
private def openingWithReturnedProjection (target picked : Expr) : MetaM Expr := do
  let actualTest ← openingHead target ``PreparationFrame.ReportTest
  let actualWriter ← openingHead (← inferType picked) ``PreparationFrame.WriterProjection
  let lemmaInfo ← getConstInfo ``PreparationFrame.ReportTest.opening_ofCanonical
  forallTelescope lemmaInfo.type fun inputs conclusion => do
    let names ← inputs.mapM fun p => p.fvarId!.getUserName
    let some j := names.idxOf? `picked | throwError "the native writer projection is missing"
    let test ← openingHead conclusion ``PreparationFrame.ReportTest
    let writer ← openingHead (← inferType inputs[j]!) ``PreparationFrame.WriterProjection
    unless names.back? == some `handle do throwError "expected the native opening handler"
    unless ← isDefEq test.getAppArgs.back! actualTest.getAppArgs.back! do
      throwError "the goal is not the opening stage"
    let mut proof := mkConst lemmaInfo.name actualTest.getAppFn.constLevels!
    for formal in inputs.pop do
      let value ← if formal == inputs[j]! then pure picked else if let some i := test.getAppArgs.idxOf? formal then
        pure actualTest.getAppArgs[i]!
      else if let some i := writer.getAppArgs.idxOf? formal then pure actualWriter.getAppArgs[i]!
      else throwError "could not read {(← formal.fvarId!.getUserName)} from the two source records"
      proof := mkApp proof value
    return proof

private def actualOpeningImplication : MetaM (Expr × Expr) := do
  let original ← getConstInfo ``SignedCalendarAt.frozenLookupAt
  let stage ← getConstInfo ``SignedCalendarAt.LookupReportOpeningAt
  forallTelescopeReducing original.type fun inputs _ => do
    let lookup := mkAppN (mkConst original.name (original.levelParams.map Level.param)) inputs
    let wanted := mkAppN (mkConst stage.name (stage.levelParams.map Level.param)) inputs
    let projection ← mkProjection lookup `projection
    let rule ← openingWithReturnedProjection wanted projection
    let .forallE name domain _ info := (← inferType rule).headBeta
      | throwError "no remaining handler for the actual report opening"
    let goal := mkForall name info domain wanted
    let proof := mkApp2 (mkConst ``id [.zero]) goal rule
    return (← mkForallFVars inputs goal, ← mkLambdaFVars inputs proof)


local elab "lookupOpeningImplicationType%" : term => do
  return (← actualOpeningImplication).1

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
/-- The native handler of the returned writer implies the opening test of that calendar. -/
abbrev SignedCalendarAt.OriginalOpeningImplication : Prop := lookupOpeningImplicationType%

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
/-- Apply the canonical opening rule on each original physical lookup. -/
theorem SignedCalendarAt.originalOpeningImplication : SignedCalendarAt.OriginalOpeningImplication := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← actualOpeningImplication).2
    Lean.Elab.Tactic.replaceMainGoal []

private def ruleAtLookup (selected : Expr) : MetaM Expr := do
  let lookup ← openingHead selected ``SignedCalendarAt.frozenLookupAt
  let rule ← mkConstWithLevelParams ``SignedCalendarAt.originalOpeningImplication
  return mkAppN rule lookup.getAppArgs

/-- Specialize the checked opening rule with the arguments of the selected physical lookup. -/
elab "originalNativeOpeningRule% " selected:term:max : term => do
  ruleAtLookup (← Lean.Elab.Term.elabTerm selected none)

/-- The native handler required by the checked opening rule on these same physical inputs. -/
elab "originalNativeOpeningHandler% " selected:term:max : term => do
  let rule ← ruleAtLookup (← Lean.Elab.Term.elabTerm selected none)
  let .forallE _ input _ _ ← whnf (← inferType rule)
    | throwError "expected the native handler of the returned opening rule"
  return input

end Diagonal

end BorderVNP
end Computability
end OAI
