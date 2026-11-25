import OAI.Computability.BorderVNP.DiagonalCalendarSelectedHostPublication
import OAI.Computability.BorderVNP.DiagonalCalendarPacketHostEntry
import OAI.Computability.BorderVNP.DiagonalIssuedHostProgramTerm
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-! # Reading the occupied private and live placements on a selected report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term TeamContraction
private def inputPosition (fields : Array Expr) (key : Name) : MetaM Nat := do
  let some pos ← fields.findIdxM? (fun x => do return (← x.fvarId!.getUserName).eraseMacroScopes == key) |
    throwError "missing original calendar input {key}"
  return pos


private def fieldOn (application : Expr) (key : Name) : MetaM Expr := do
  let info ← getConstInfo application.getAppFn.constName!
  forallTelescope info.type fun parameters _ => do
    return application.getAppArgs[← inputPosition parameters key]!

private def allRegisteredKeys : TermElabM Expr := do
  let lookup ← mkConstWithLevelParams ``SignedCalendarAt.frozenLookupAt
  let publication ← mkConstWithLevelParams ``SignedCalendarAt.frozenSelectedHostPublication
  forallTelescope (← inferType lookup) fun original _ => do
    let prototype := mkAppN lookup original
    let some model ← whnfUntil (← inferType prototype) ``PreparationFrame.SelectedLookupSites |
      throwError "expected the original lookup"
    let some planner ← whnfUntil (← fieldOn model `task) ``SignedCalendarAt.frozenPlannerTask |
      throwError "missing the original planner occupation"
    let oper := original[← inputPosition original `oper]!
    let routing ← mkProjection oper `routing
    let values := original[← inputPosition original `values]!
    let history := original[← inputPosition original `hist]!
    let entry := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenHostProgramEntry)
      (planner.getAppArgs ++ #[routing,values,history])
    let layout := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites) planner.getAppArgs
    let bank ← mkProjection layout `publicWords
    let cal := mkAppN publication original
    forallBoundedTelescope (← inferType cal) (some 6) fun indices _ => do
      unless indices.size == 6 do throwError "expected all original host coordinates"
      let reached :=  mkAppN cal indices
      let site ← exprToSyntax indices[3]!
      let x ← exprToSyntax indices[4]!
      let u ← exprToSyntax indices[5]!
      let regs ← exprToSyntax (mkApp bank indices[5]!)
      let reader ← exprToSyntax entry
      withLetDecl `physicalOnOriginal (← inferType reached) reached fun physical => do
        let p ← exprToSyntax physical
        let epoch := mkIdent `epoch
        let written := mkIdent `published
        let middle := mkIdent `epochMemory
        let result ← elabTerm (← `(
          let recorded := (originalLookupSites% $site) $x $u
          issuedHostProgramOn% $reader $regs $p.2.2 (issuedField% $epoch:ident recorded)
            (issuedField% $written:ident recorded) (issuedField% $middle:ident recorded) $p.2.1)) none
        synthesizeSyntheticMVarsNoPostponing
        let result ← instantiateMVars result
        if result.hasMVar || result.hasSorry then throwError "incomplete native address proof"
        let point ← mkLetFVars #[physical] result (generalizeNondepLet := false)
        mkLambdaFVars (original ++ indices) point

private def publish {P : Prop} (actual : P) : PSigma (fun p : Prop => p) := ⟨P,actual⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 18000000 in
private noncomputable def completeKeys : PSigma (fun p : Prop => p) := by
  run_tac
    let native ← allRegisteredKeys
    let packaged := mkAppN (← mkConstWithLevelParams ``publish) #[← inferType native,native]
    (← Lean.Elab.Tactic.getMainGoal).assign packaged
    Lean.Elab.Tactic.replaceMainGoal []

/-- At every registered selection of this actual numerical calendar, read the two occupied
placement tables, the original writer, and the machine's published memory. -/
theorem SignedCalendarAt.frozenSelectedHostKeys : completeKeys.1 := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign
      (mkProj ``PSigma 1 (← mkConstWithLevelParams ``completeKeys))
    Lean.Elab.Tactic.replaceMainGoal []

private def keysAtInitialSelection : TermElabM Expr := do
  let lookup ← mkConstWithLevelParams ``SignedCalendarAt.frozenLookupAt
  let keys ← mkConstWithLevelParams ``SignedCalendarAt.frozenSelectedHostKeys
  forallTelescope (← inferType lookup) fun original _ => do
    let candidate := mkAppN lookup original
    let some model ← whnfUntil (← inferType candidate) ``PreparationFrame.SelectedLookupSites |
      throwError "missing the acquired initial lookup"
    let actual := mkAppN keys (original ++ #[← fieldOn model `wire,← fieldOn model `same,← fieldOn model `F,candidate])
    mkLambdaFVars original actual
set_option cleanup.letToHave false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 18000000 in
private noncomputable def bareKeys : PSigma (fun p : Prop => p) := by
  run_tac
    let native ← keysAtInitialSelection
    let packaged := mkAppN (← mkConstWithLevelParams ``publish) #[← inferType native,native]
    (← Lean.Elab.Tactic.getMainGoal).assign packaged
    Lean.Elab.Tactic.replaceMainGoal []

/-- Read these same tables directly on the frame acquired by the bare lookup. -/
theorem SignedCalendarAt.frozenLookupHostKeys : bareKeys.1 := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign
      (mkProj ``PSigma 1 (← mkConstWithLevelParams ``bareKeys))
    Lean.Elab.Tactic.replaceMainGoal []


end Diagonal

end BorderVNP
end Computability
end OAI
