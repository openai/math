import OAI.Computability.BorderVNP.DiagonalCalendarMarkersAtReportedExterior
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarOwnerAdmission

/-! # The issued marker packet on every original reported field and receiving team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ReportedFieldMarkers
open Lean Meta Elab Term Command RoutingISA RoutingISA.Evaluator TeamContraction

set_option maxRecDepth 16000
set_option maxHeartbeats 4200000
set_option synthInstance.maxSize 4000

private def projection (x : Expr) (i : Nat) : MetaM Expr := do
  let t ← whnf (← inferType x)
  let some n := t.getAppFn.constName? | throwError "missing native product"
  return mkProj n i x

private def indexed (args : Array Expr) (key : Name) : MetaM Nat := do
  let some ix ← args.findIdxM? fun x => return (← x.fvarId!.getUserName) == key |
    throwError "missing original input {key}"
  return ix

/-- The registered native owner carries its actual source exterior as an index. -/
private def ownerIndex (owner : Expr) : TermElabM (Expr × Expr) := do
  let scope ← instantiateLCtxMVars (← getLCtx)
  let ty ← match Kernel.check (← getEnv) scope (ShareCommon.shareCommon owner) with
    | .ok t => pure t
    | .error err => throwError "invalid original ownership: {err.toMessageData (← getOptions)}"
  let some receipt ← whnfUntil ty ``PreparationFrame.ReturnedOwnershipAt |
    throwError "the original cell owner has no attained exterior"
  let sig ← getConstInfo ``PreparationFrame.ReturnedOwnershipAt
  forallBoundedTelescope sig.type (some receipt.getAppNumArgs) fun args _ =>
    return (receipt.getAppArgs[← indexed args `origin]!,receipt.getAppArgs[← indexed args `R]!)

private def markerOnField (inputs : Array Expr) (checks f : Expr) : TermElabM (Expr × Expr) := do
  let take := fun (key : Name) => do return inputs[← indexed inputs key]!
  let syntaxOf := fun (key : Name) => do exprToSyntax (← take key)
  let pin ← projection f 0
  let tail ← projection f 1
  let hist ← projection tail 0
  let parts ← projection tail 1
  let route ← projection (← projection parts 0) 0
  let claim ← projection (← projection parts 1) 0
  let cal ← syntaxOf `cal
  let oper ← syntaxOf `oper
  let position ← syntaxOf `position
  let chart ← syntaxOf `chart
  let reader ← syntaxOf `reader
  let charge ← syntaxOf `chargeFit
  let values ← syntaxOf `values
  let qpos ← syntaxOf `qpos
  let hi ← exprToSyntax hist
  let rt ← exprToSyntax route
  let honest ← elabTerm (← `(SignedCalendarAt.frozenRouteAllowedForOwner $cal ($oper).grid $qpos $position $chart $reader $charge $values $hi)) none
  let declared ← elabTerm (← `(SignedPrep.routeBroadcast (SignedCalendarAt.frozenPlannerTask $cal ($oper).grid $qpos $position $chart $reader $charge).cube _ $rt)) none
  let entries ← elabTerm (← `(SignedCalendarAt.frozenFrameEntries $cal ($oper).grid $qpos $position $chart $reader $charge $values)) none
  synthesizeSyntheticMVarsNoPostponing
  let allowed := mkApp (← instantiateMVars honest) route
  let raw ← instantiateMVars declared
  let issued ← nativeWriterOnCheckedRoutes checks
  let w := issued.getAppArgs
  let owner := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates)
    (w.extract 0 (w.size-1) ++ #[← instantiateMVars entries,checks,f])
  let (anchor, teamPred) ← ownerIndex owner
  let family := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.markersAtOriginalReportedExterior) inputs
  let observed := mkAppN family #[pin,hist,claim,raw,allowed,anchor]
  let team := mkApp (Lean.mkConst ``Fin) (mkApp (Lean.mkConst ``Nat.succ) teamPred)
  withLocalDeclD `u team fun u => do
    let marked := mkApp observed u
    let ctx ← instantiateLCtxMVars (← getLCtx)
    let type ← match Kernel.check (← getEnv) ctx (ShareCommon.shareCommon marked) with
      | .ok t => pure t
      | .error err => throwError "invalid marker on the original field: {err.toMessageData (← getOptions)}"
    let some predicate ← whnfUntil type ``SignedCalendarAt.frozenIssuedMarkerPacket |
      throwError "expected the complete packet on this returned geometry"
    let vars := inputs ++ #[f,u]
    return (← mkForallFVars vars predicate,← mkLambdaFVars vars marked)

run_cmd liftTermElabM do
  let prior ← getConstInfo ``SignedCalendarAt.routeReadbackOnOriginalReports
  let (type,proof) ← forallTelescope prior.type fun params _ => do
    let inputs := params.extract 0 ((← indexed params `reports)+1)
    let checks := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeInputsOnOriginalReports) inputs
    let writer ← nativeWriterOnCheckedRoutes checks
    let .forallE _ field _ _ ← whnf (← inferType writer) | throwError "missing true native field"
    withLocalDeclD `f field fun f => markerOnField inputs checks f
  let proof := ShareCommon.shareCommon (← instantiateMVars proof)
  if proof.hasFVar || proof.hasMVar || proof.hasSorry then throwError "unclosed marker proof"
  let name := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.fundedMarkersOnOriginalReports
  let signature := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.OriginalReportedMarkerStatement
  let fullType := ShareCommon.shareCommon type
  addDecl (.defnDecl {name := signature, levelParams := prior.levelParams, type := .sort .zero, value := fullType, hints := .abbrev, safety := .safe})
  let some _ := (← getEnv).toKernelEnv.find? signature | throwError "unregistered marker proposition"
  addDocStringCore signature "The issued marker packet on the returned geometry of each original field and receiving team."
  let target := Lean.mkConst signature (prior.levelParams.map Level.param)
  addDecl (.thmDecl {name, levelParams := prior.levelParams, type := target, value := proof})
  let some _ := (← getEnv).toKernelEnv.find? name | throwError "unregistered marker theorem"
  addDocStringCore name "The registered field’s own returned geometry contains the issued marker words, inverse ranks and marker bounds at the exterior of its actual owner."

end Diagonal.ReportedFieldMarkers

end BorderVNP
end Computability
end OAI
