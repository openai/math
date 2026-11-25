import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalSelectedHostFrameTerm
import OAI.Computability.BorderVNP.DiagonalHostPublicationAtSiteTerm

/-! # Physical publication at every candidate admitted by an original calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction

private def inputPosition (fields : Array Expr) (key : Name) : MetaM Nat := do
  let some pos ← fields.findIdxM? (fun x => do return (← x.fvarId!.getUserName).eraseMacroScopes == key) |
    throwError "missing original calendar input {key}"
  return pos

private def atSelected (model value : Expr) (field : Name) : Expr :=
  mkAppN (Lean.mkConst field model.getAppFn.constLevels!) (model.getAppArgs.push value)

/-- Bind the submitted wire and equal declared header, its initial frame, and the
actual selected sites on that frame, preserving the implicit public arguments. -/
private def bindOriginalFrame (sites : Expr) (next : Expr → TermElabM Expr) : TermElabM Expr := do
  let rec bind (names : List Name) (family type : Expr) : TermElabM Expr := do
    match names with
    | [] => withLocalDeclD `s family fun selected => do
      mkLambdaFVars #[selected] (← next selected)
    | name :: rest =>
      let .forallE _ domain codomain _ ← whnf type | throwError "missing original wire, extent or initial frame"
      withLocalDecl name .implicit domain fun item => do
        let tail ← bind rest (mkApp family item) (codomain.instantiate1 item)
        mkLambdaFVars #[item] tail
  bind [`wire,`extent,`frame] sites (← inferType sites)

private def calibratedPublication : TermElabM Expr := do
  let lookup ← mkConstWithLevelParams ``SignedCalendarAt.frozenLookupAt
  forallTelescopeReducing (← inferType lookup) fun original _ => do
    let prototype := mkAppN lookup original
    let some model ← whnfUntil (← inferType prototype) ``PreparationFrame.SelectedLookupSites |
      throwError "expected the original calendar's registered lookup"
    let decl ← getConstInfo ``PreparationFrame.SelectedLookupSites
    let field := fun name => do
      forallTelescope decl.type fun ps _ => do
        return model.getAppArgs[← inputPosition ps name]!
    let some planner ← whnfUntil (← field `task) ``SignedCalendarAt.frozenPlannerTask |
      throwError "expected the original calibrated planner task"
    let data ← planner.getAppArgs.mapM exprToSyntax
    let plannerSyntax ← `(@SignedCalendarAt.frozenPlannerTask $data*)
    let oper := original[← inputPosition original `oper]!
    let routing ← exprToSyntax (← mkProjection oper `routing)
    let values ← exprToSyntax original[← inputPosition original `values]!
    let hist ← exprToSyntax original[← inputPosition original `hist]!
    let family := atSelected model prototype ``PreparationFrame.SelectedLookupSites.SitesAt
    let allSites ← bindOriginalFrame family fun selected => do
      let some actual ← whnfUntil (← inferType selected) ``PreparationFrame.SelectedLookupSites |
        throwError "expected the sites recorded on the declared original frame"
      let sites := atSelected actual selected ``PreparationFrame.SelectedLookupSites.returnedSite
      forallBoundedTelescope (← inferType sites) (some 2) fun here _ => do
        unless here.size==2 do throwError "expected the recorded exterior and team"
        let s ← exprToSyntax selected
        let x ← exprToSyntax here[0]!
        let u ← exprToSyntax here[1]!
        let recorded ← elabTerm (← `(nativeHostPublicationAt% $plannerSyntax $routing $values $hist $s $x $u)) none
        synthesizeSyntheticMVarsNoPostponing
        let physical ← instantiateMVars (mkProj ``And 1 recorded)
        if physical.hasMVar || physical.hasSorry then throwError "unresolved native publication data"
        mkLambdaFVars here physical
    return ← mkLambdaFVars original allSites

private def publish {P : Prop} (actual : P) : PSigma (fun p : Prop => p) := ⟨P,actual⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 18000000 in
private noncomputable def originalCalendarPublication : PSigma (fun p : Prop => p) := by
  run_tac
    let native ← calibratedPublication
    let packaged := mkAppN (← mkConstWithLevelParams ``publish) #[← inferType native,native]
    (← Lean.Elab.Tactic.getMainGoal).assign packaged
    Lean.Elab.Tactic.replaceMainGoal []

/-- At every registered selection of this actual numerical calendar, the original
header, packet memory and signed pin are published on its recorded physical state. -/
theorem SignedCalendarAt.frozenSelectedHostPublication : originalCalendarPublication.1 := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign
      (mkProj ``PSigma 1 (← mkConstWithLevelParams ``originalCalendarPublication))
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
