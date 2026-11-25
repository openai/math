import OAI.Computability.BorderVNP.DiagonalOriginalHostSiblingArguments

/-! # The original report before reading host cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term
open RoutingISA.Evaluator.SignedPrep

private def selectedReturn (sites exterior : Expr) : MetaM Expr := do
  let some selection ← whnfUntil (← inferType sites) ``PreparationFrame.SelectedLookupSites
    | throwError "expected the original selected frame and its sites"
  let stages := mkAppN (mkConst ``PreparationFrame.SelectedLookupSites.returnedSiteStages
    selection.getAppFn.constLevels!) (selection.getAppArgs ++ #[sites,exterior])
  forallBoundedTelescope (← inferType stages) (some 1) fun teams _ => do
    let observed := mkProj ``And 0 (mkAppN stages teams)
    let some existsSite ← whnfUntil (← inferType observed) ``Exists
      | throwError "missing the original reached site"
    let returned := mkAppN (mkConst ``Exists.choose_spec existsSite.getAppFn.constLevels!)
      (existsSite.getAppArgs.push observed)
    mkLambdaFVars teams (mkProj ``And 0 returned)

private def onReturnedTeams (reader returned : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType returned) (some 1) fun teams property => do
    let some observed ← whnfUntil property ``CandidateSite.OnReturn
      | throwError "expected the complete native candidate return"
    let fields := observed.getAppArgs
    let start := fields.size-15
    -- The reader consumes the two charges before the final registers and RAM.
    let mut data := #[]
    for i in #[0,1,2,3,4,5,6,7,8,9,10,13,14,11,12] do
      let v := fields[start+i]!
      if 1 ≤ i && i ≤ 7 then
        if v.containsFVar teams[0]!.fvarId! then throwError "a common report word varies across teams"
        data := data.push v
      else data := data.push (← mkLambdaFVars teams v)
    return mkAppN reader (data.push returned)

/-- Apply the signed host reader to the same registered sites, their reported
exterior, the original writer operands, and the three reached report stages. -/
elab "applyOriginalHostOnReplay%" worker:term:max sites:term:max exterior:term:max
    "at" "[" values:term,* "]" : term => do
  let current ← elabTerm sites none
  let x ← elabTerm exterior none
  let read ← elabTerm (← `(originalHostAtSibling% $worker $sites)) none
  let inputs ← values.getElems.mapM fun v => elabTerm v none
  let returned ← selectedReturn current x
  onReturnedTeams (mkAppN read inputs) returned

end TeamContraction

end BorderVNP
end Computability
end OAI
