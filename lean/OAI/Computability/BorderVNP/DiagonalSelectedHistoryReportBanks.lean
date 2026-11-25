import OAI.Computability.BorderVNP.DiagonalCandidateBankReportTests

/-! # Transferring the returned publication and capacities to the observed team history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction
open Lean Meta Elab Term RoutingISA.Evaluator.SignedPrep

private def lookupAndReport (selected data : Expr) (report : Name) : MetaM (Expr × Expr) := do
  let some chosen ← whnfUntil (← inferType selected) ``PreparationFrame.SelectedLookupSites
    | throwError "expected the selected native lookup"
  let some inhabited ← whnfUntil (← inferType data) ``Nonempty
    | throwError "expected an attained report"
  let some reached ← whnfUntil inhabited.appArg! report | throwError "expected attained {report}"
  return (chosen, reached)

private def historyReportAt (method report : Name) (chosen exterior history observation data : Syntax) : TermElabM Expr := do
  let selected ← elabTerm chosen none
  let x ← elabTerm exterior none
  let H ← elabTerm history none
  let actual ← elabTerm observation none
  let claim ← elabTerm data none
  let (native, reported) ← lookupAndReport selected claim report
  let tail ← forallBoundedTelescope (← inferType actual) (some 1) fun teams facts => do
    unless teams.size == 1 do throwError "expected one observation per issued team"
    let some pair ← whnfUntil facts ``And | throwError "expected a public register observation"
    let some rest ← whnfUntil pair.appArg! ``And | throwError "expected an observed macro library and a tail"
    mkLambdaFVars teams rest.appArg!
  let sig ← getConstInfo method
  forallTelescope sig.type fun args _ => do
    let names ← args.mapM fun b => b.fvarId!.getUserName
    let some c := names.idxOf? `chosen | throwError "missing selected lookup in method"
    let some k := names.idxOf? `data | throwError "missing attained report in method"
    let (lookupPattern, reportPattern) ← lookupAndReport args[c]! args[k]! report
    let formal := lookupPattern.getAppArgs ++ reportPattern.getAppArgs
    let values := native.getAppArgs ++ reported.getAppArgs
    let explicit : List (Name × Expr) := [(`chosen,selected),(`x,x),(`H,H),(`tail,tail),(`actual,actual),(`data,claim)]
    let supplied ← args.mapM fun formalArg => do
      let key ← formalArg.fvarId!.getUserName
      if let some (_, value) := explicit.find? (·.1 == key) then return value
      let some j := formal.findIdx? (· == formalArg) | throwError "missing original {key} for {method}"
      return values[j]!
    let fromLookup := lookupPattern.getAppFn.constLevels!.zip native.getAppFn.constLevels!
    let fromReport := reportPattern.getAppFn.constLevels!.zip reported.getAppFn.constLevels!
    let levels ← sig.levelParams.mapM fun param => do
      let some (_, actual) := (fromLookup ++ fromReport).find? (fun (l,_) => l == .param param)
        | throwError "missing original universe {param} for {method}"
      return actual
    return mkAppN (Lean.mkConst method levels) supplied

/-- Transfer the original publication to these observed processor histories. -/
elab "originalPublicationOnActual% " chosen:term:max x:term:max history:term:max actual:term:max data:term:max : term =>
  historyReportAt ``PreparationFrame.SelectedLookupSites.publication_onHistory ``CandidateReportPublication
    chosen x history actual data

/-- Transfer the original capacity witness to these observed processor histories. -/
elab "originalCapacityOnActual% " chosen:term:max x:term:max history:term:max actual:term:max data:term:max : term =>
  historyReportAt ``PreparationFrame.SelectedLookupSites.capacity_onHistory ``CandidateReportCapacity
    chosen x history actual data

end TeamContraction

end BorderVNP
end Computability
end OAI
