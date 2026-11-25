import OAI.Computability.BorderVNP.DiagonalCalendarOwnedHostWordsType
import OAI.Computability.BorderVNP.DiagonalReportSourcePlacement

/-! # The compact roster and the registered source read the same W owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

private def registeredRosterReading (proof : Bool) : TermElabM Expr := do
  let host ← mkConstWithLevelParams ``SignedCalendarAt.OwnedHostWords
  forallTelescopeReducing (← inferType host) fun inputs _ => do
    let d := inputs.size - 3
    let tail := inputs.extract d inputs.size
    let names ← tail.mapM fun v => return (← v.fvarId!.getUserName).eraseMacroScopes
    unless names == #[`v,`input,`owned] do throwError "expected the registered route, input and native return"
    let registered := mkAppN host inputs
    let some words ← whnfUntil registered ``ExternalSew.Fragments.SourceWords |
      throwError "expected the registered W reading"
    let reader := Lean.mkConst ``SignedCalendarAt.frozenHostTeam host.constLevels!
    let identifies := mkApp (mkAppN reader (inputs.extract 0 d)) tail[0]!
    let original ← exprToSyntax tail[2]!
    let view ← elabTerm (← `(fun t => FiniteEvaluator.OpenSuffix.hostImage
      (($original).pub t 0).val (RoutingISA.readings (($original).output t)))) none
    let roster ← forallBoundedTelescope (← inferType identifies) (some 1) fun cell result => do
      let some equality ← whnfUntil result ``Eq | throwError "expected the true owner of each W cell"
      mkLambdaFVars cell (mkApp view equality.getAppArgs[1]!)
    let args := words.getAppArgs
    let onRoster := mkAppN words.getAppFn ((args.extract 0 (args.size-1)).push roster)
    withLocalDeclD `words onRoster fun actual => do
      if proof then
        let moved ← mkAppM ``ExternalSew.Fragments.SourceWords.reindexOwners #[view,actual,identifies]
        mkLambdaFVars (inputs.push actual) (← mkExpectedTypeHint moved registered)
      else
        mkForallFVars (inputs.push actual) registered

local elab "rosterReadingType%" : term => registeredRosterReading false

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
/-- Native source words on each compact roster cell imply the registered reading
on the same original route, public pin, and joint hardware return. -/
abbrev SignedCalendarAt.RegisteredWordsFromRoster : Prop := rosterReadingType%

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
/-- The inverse compact order recovers exactly the selected host of every cell. -/
theorem SignedCalendarAt.frozenHostWordsOnRoster : SignedCalendarAt.RegisteredWordsFromRoster := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← registeredRosterReading true)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
