import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalReturnedDispatchOriginalRows
import OAI.Computability.BorderVNP.DiagonalDispatchReportPacketCells
import OAI.Computability.BorderVNP.DiagonalDispatchReportPhysicalFrame

/-! # Dispatch rows of the original reported owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term
open private originalOwner from OAI.Computability.BorderVNP.DiagonalAttainedReportOperands

/-- The four remaining native arguments are the physical fit, fragment count,
emitter and control address read. -/
private def reportsFromAttainedTeam (candidate atVisit team : Expr) : MetaM Expr := do
  let (starts,active,length) ← originalOwner atVisit
  let some received ← whnfUntil (← inferType candidate) ``ReturnedCandidateReports |
    throwError "expected the report retained by the original owner"
  let method := ``ReturnedCandidateReports.reportsAtOwnDispatch
  let rule ← getConstInfo method
  forallTelescope rule.type fun params _ => do
    let names ← params.mapM fun p => p.fvarId!.getUserName
    let some source := names.idxOf? `actual | throwError "missing the original returned source"
    let some cut := names.idxOf? `fit | throwError "missing the issued report fit"
    unless names.extract cut names.size == #[`fit,`cells,`emitted,`pointer] do
      throwError "expected the original fit, fragment count, emitter and pointer"
    let some pattern ← whnfUntil (← inferType params[source]!) ``ReturnedCandidateReports |
      throwError "expected the formal returned candidate in the native rule"
    let recorded := received.getAppArgs
    let scheme := pattern.getAppArgs
    let native := [(`actual,candidate),(`U,starts),(`active,active),(`n,length),(`u,team)]
    let originalInputs ← (params.extract 0 cut).mapM fun param => do
      let name ← param.fvarId!.getUserName
      if let some value := native.lookup name then return value
      let some i := scheme.findIdx? (· == param) |
        throwError "missing retained candidate coordinate {name}"
      return recorded[i]!
    return mkAppN (mkConst method received.getAppFn.constLevels!) originalInputs

private def matchingSpines (head : Name) (a b : Expr) : MetaM (Array (Expr × Expr)) := do
  let some formal ← whnfUntil a head | throwError "missing method signature head {head}"
  let some actual ← whnfUntil b head | throwError "recorded proof has no {head} spine"
  unless formal.getAppNumArgs == actual.getAppNumArgs do throwError "different arity for {head}"
  return formal.getAppArgs.zip actual.getAppArgs

/-- Reuse the recorded row arguments and the actual sides of the equality.
The only nested operands come from sourceCells or the readings of publish. -/
private def dispatchMethod (method : Name) (rows eq : Expr) : MetaM Expr := do
  let f ← getConstInfo method
  unless f.levelParams.isEmpty do throwError "expected monomorphic report method"
  forallTelescope f.type fun args _ => do
    let cut := args.size-2
    let outer ← matchingSpines ``DispatchReportRows (← inferType args[cut]!) (← inferType rows)
    let equality ← matchingSpines ``Eq (← inferType args.back!) (← inferType eq)
    let mut inputs := outer ++ equality
    for head in [``DiagonalTallyCellReports.ReportDirectory.sourceCells, ``readings, ``Packing.Directory.ISA.publish] do
      if let some (formal,actual) := inputs.find? fun p => p.1.isAppOf head then
        inputs := inputs ++ (← matchingSpines head formal actual)
    let fixed ← (args.extract 0 cut).mapM fun v => do
      let some (_,e) := inputs.find? fun p => p.1==v
        | throwError "unaccounted report parameter {← v.fvarId!.getUserName}"
      pure e
    return mkAppN (mkConst method) (fixed ++ #[rows,eq])

/-- Both transformations of one complete physical row scan. -/
private def dispatchMethods (rows names frame : Expr) : MetaM (Expr × Expr) := do
  let first ← dispatchMethod ``DispatchReportRows.atOwnerWords rows names
  return (first, ← dispatchMethod ``DispatchReportRows.atPhysicalFrame first frame)

/-- Obtain the true returned report at each field and apply the native row
operations after its physical team, emitter and pointer have been fixed. -/
elab (name := originalDispatchReports) "originalDispatchReports% " writers:term:max retained:term:max : term => do
  let native ← elabTerm writers none
  let reports ← elabTerm retained none
  let .forallE _ fields _ _ ← whnf (← inferType native) |
    throwError "expected the original submitted field"
  withLocalDeclD `f fields fun field => do
    let found := mkApp reports field
    let received ← exprToSyntax found
    let actual ← elabTerm (← `(($received).1.choose_spec.choose_spec.some)) none
    let same := mkProj ``And 1 found
    let names := mkProj ``And 1 (mkProj ``And 1 (mkApp native field))
    let (starts,_,_) ← originalOwner same
    let .forallE _ teams _ _ ← whnf (← inferType starts) |
      throwError "expected native starts on the original teams"
    withLocalDeclD `u teams fun team => do
      let service ← reportsFromAttainedTeam actual same team
      let opened ← mkProjection actual `opened
      let frame ← mkProjection (mkApp (mkProj ``And 1 opened) team) `frame
      forallBoundedTelescope (← inferType service) (some 4) (whnfType:=true) fun inputs _ => do
        unless inputs.size==4 do throwError "expected the issuing fit, cells, emitter and pointer"
        let original := mkAppN service inputs
        let (_,physical) ← dispatchMethods original names frame
        let coordinates := #[field,team] ++ inputs
        let statement ← mkForallFVars coordinates (← inferType physical)
        let proof ← mkLambdaFVars coordinates physical
        let prop := mkSort .zero
        let identity := mkLambda `p .default prop (.bvar 0)
        return mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[prop,identity,statement,proof]

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
