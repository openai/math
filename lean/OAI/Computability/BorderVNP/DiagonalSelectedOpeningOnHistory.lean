import OAI.Computability.BorderVNP.DiagonalCandidateBankReportTests

/-! # Return the observed opener to its original registered lookup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Tactic
open RoutingISA.Evaluator.SignedPrep

private def openingIndices (model actual : Expr) : Array (FVarId × Expr) :=
  (model.getAppArgs.zip actual.getAppArgs).filterMap fun (argument, value) =>
    if argument.isFVar then some (argument.fvarId!, value) else none

private def observedTail (actual : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType actual) (some 1) fun teams statement => do
    unless teams.size == 1 do throwError "expected one observation per team"
    let some publication ← whnfUntil statement ``And | throwError "missing the returned public words"
    let some macros ← whnfUntil publication.appArg! ``And | throwError "missing the returned macro table"
    mkLambdaFVars teams macros.appArg!

/-- Transfer the original opening goal to the same selected site on the observed
team history. The remaining goal is its opening on that specific history. -/
elab "applyOriginalReportOpening" chosen:term:max exterior:term:max history:term:max actual:term:max : tactic =>
  withMainContext do
    let caller ← getLCtx
    let instances ← getLocalInstances
    let lookup ← elabTerm chosen none
    let x ← elabTerm exterior none
    let h ← elabTerm history none
    let seen ← elabTerm actual none
    let tail ← observedTail seen
    let goal ← getMainGoal
    let some selected ← whnfUntil (← inferType lookup) ``PreparationFrame.SelectedLookupSites
      | throwErrorAt chosen "expected the selected sites of the original lookup"
    let some opening ← whnfUntil (← goal.getType) ``CandidateReportOpening
      | throwError "expected an opening at the original registered site"
    let rule ← mkConstWithLevelParams ``PreparationFrame.SelectedLookupSites.reportOpening_of_siteOnHistory
    forallTelescope (← inferType rule) fun params conclusion => do
      let mut indices := openingIndices conclusion opening
      for param in params do
        if (← param.fvarId!.getUserName) == `chosen then
          let some shape ← whnfUntil (← inferType param) ``PreparationFrame.SelectedLookupSites
            | throwError "missing the lookup in the opening rule"
          indices := indices ++ openingIndices shape selected
      let mut applyRule := rule
      let mut ty ← inferType rule
      for param in params do
        let name ← param.fvarId!.getUserName
        if name == `data then
          let data ← withLCtx caller instances (mkFreshExprSyntheticOpaqueMVar ty.bindingDomain!)
          goal.assign (mkApp applyRule data)
          replaceMainGoal [data.mvarId!]
          return
        let value ← match name with
          | `chosen => pure lookup
          | `x => pure x
          | `H => pure h
          | `tail => pure tail
          | `actual => pure seen
          | _ => do
            let some (_, value) := indices.find? (·.1 == param.fvarId!)
              | throwError "the registered lookup and opening do not determine {name}"
            pure value
        applyRule := mkApp applyRule value
        ty := ty.bindingBody!.instantiate1 value
      throwError "missing the observed opening in the transfer rule"

end TeamContraction

end BorderVNP
end Computability
end OAI
