import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarHostWordsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarHostReportAtCells
import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalReturnedEntryPlacement

/-! # The returned report memory on the original registered fields and teams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.OriginalRegisteredMixed
open Lean Meta Elab Term RoutingISA RoutingISA.Evaluator TeamContraction FiniteEvaluator SignedPrep
set_option maxRecDepth 26000
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 4000
set_option cleanup.letToHave false

private def headed (term : Expr) (n : Name) : MetaM Expr := do
  let some e ← whnfUntil term n | throwError "expected {n} in the original report"
  return e

private def number (type : Expr) (n : Name) : MetaM Nat := do
  forallTelescope type fun xs _ => do
    let some i ← xs.findIdxM? (fun x => return (← x.fvarId!.getUserName) == n) | throwError "missing {n}"
    return i

private def argument (term : Expr) (n : Name) : MetaM Expr := do
  let info ← getConstInfo term.getAppFn.constName!
  let i ← number info.type n
  return term.getAppArgs[i]!

private def project (term : Expr) (i : Nat) : MetaM Expr := do
  let type ← whnf (← inferType term)
  let some name := type.getAppFn.constName? | throwError "missing original record at {i}"
  return mkProj name i term

private def field (op : Name) (val : Expr) : MetaM Expr := do
  let some spec ← getProjectionFnInfo? op | throwError "not an original field: {op}"
  let type ← whnf (← inferType val)
  return mkProj type.getAppFn.constName! spec.i val

private def chosenReport (found : Expr) : MetaM Expr := do
  let mut w := mkProj ``And 0 found
  for _ in [0:2] do
    let e ← headed (← inferType w) ``Exists
    w := mkAppN (Lean.mkConst ``Classical.choose_spec e.getAppFn.constLevels!) (e.getAppArgs.push w)
  let p ← headed (← inferType w) ``Nonempty
  return mkAppN (Lean.mkConst ``Classical.choice p.getAppFn.constLevels!) (p.getAppArgs.push w)

private def abstractAt (xs : Array Expr) (result : Expr × Expr) : MetaM (Expr × Expr) := do
  return (← mkLambdaFVars xs result.1, ← mkForallFVars xs result.2)

private def letAt (n : Name) (v : Expr) (act : Expr → TermElabM (Expr × Expr)) : TermElabM (Expr × Expr) := do
  withLetDecl n (← inferType v) v fun x => do
    let (proof, goal) ← act x
    return (← mkLetFVars #[x] proof (generalizeNondepLet := false),
      ← mkLetFVars #[x] goal (generalizeNondepLet := false))

private def atTeam (locate f route input endRows starts active id cube u C visit host : Expr) :
    TermElabM (Expr × Expr) := do
  let us ← exprToSyntax u
  let atV ← exprToSyntax visit
  let c ← exprToSyntax C
  let receipt ← elabTerm (← `(preparedOnAttainedOwner% $c $atV $us)) none
  letAt `prepared receipt fun prepared => do
    let earlier := mkProj ``And 0 prepared
    let same := mkProj ``And 1 prepared
    let sa ← headed (← inferType same) ``SignedPrep.SameReportCells
    let chart ← argument sa `l
    let cells ← argument sa `cs
    let Ctype ← headed (← inferType C) ``SignedPrep.ReturnedCandidateReports
    let raw ← argument Ctype `raw
    let declaration := mkApp2 (← mkConstWithLevelParams ``SignedPrep.decodedBroadcast) cube raw
    let axis := mkProj ``Prod 0 declaration
    let U ← exprToSyntax starts
    let op ← exprToSyntax id
    let run ← exprToSyntax (mkApp active u)
    let V ← elabTerm (← `(PinStart.visits $op $U $run)) none
    let advance ← field ``SignedPrep.Visits.controls V
    let reported ← field ``SignedPrep.Visits.reports V
    let opened := mkProj ``And 1 (← field ``SignedPrep.ReturnedCandidateReports.opened C)
    let (sections,ready) ← withLocalDeclD `v (← inferType u) fun v => do
      let entry ← exprToSyntax (mkApp opened v)
      let ok ← elabTerm (← `(($entry).ready)) none
      let rt ← headed (← inferType ok) ``OpenSuffix.Ready
      return (← mkLambdaFVars #[v] rt.getAppArgs[0]!, ← mkLambdaFVars #[v] ok)
    let entry ← exprToSyntax (mkApp opened u)
    let pos ← elabTerm (← `(originalPaidPlacement% $entry)) none
    let read := mkAppN locate #[route,input,endRows,u,advance,reported,sections,ready,pos,axis,chart,cells,same,
      mkProj ``And 0 earlier,mkProj ``And 1 earlier,mkApp host f]
    let goal ← headed (← inferType read) ``Exists
    return (read,goal)

private def atField (f host candidate : Expr) (calibrated : Array Expr) : TermElabM (Expr × Expr) := do
  letAt `originalReport (mkApp candidate f) fun found => do
    letAt `C (← chosenReport found) fun C => do
      let visit := mkProj ``And 1 found
      let eq ← headed (← inferType visit) ``Eq
      let endRows := eq.getAppArgs[1]!
      let actual ← headed endRows ``PinStart.ownedVisits
      let starts ← argument actual `S
      let active ← argument actual `p
      let id ← argument actual `id
      let cube ← argument actual `ar
      let tail ← project f 1
      let history ← project tail 0
      let route ← project (← project (← project tail 1) 0) 0
      let input ← project f 0
      let locate ← project (mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenHostReportAtCells)
        (calibrated.push history)) 1
      let teams ← whnf (← inferType starts)
      withLocalDeclD `u teams.bindingDomain! fun u => do
        let observed ← atTeam locate f route input endRows starts active id cube u C visit host
        abstractAt #[u] observed

private def compileReport : TermElabM Expr := do
  let source ← getConstInfo ``SignedCalendarAt.routeInputsOnOriginalReports
  let n := (← number source.type `reports)+1
  forallBoundedTelescope source.type (some n) fun cal _ => do
    let checks := mkAppN (← mkConstWithLevelParams source.name) cal
    let candidate := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.reportedCandidateOnOriginalReports) cal
    let host := mkProj ``PLift 0 (mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedHostSourceOnOriginalReports) cal)
    let fixed ← forallBoundedTelescope (← inferType checks) (some 3) fun _ checked => do
      let eligible ← headed checked ``SignedCalendarAt.FrozenRouteChecks
      let valuesAt ← number (← getConstInfo ``SignedCalendarAt.FrozenRouteChecks).type `values
      return eligible.getAppArgs.extract 0 (valuesAt+1)
    let fieldType ← whnf (← inferType candidate)
    let (proof,goal) ← withLocalDeclD `f fieldType.bindingDomain! fun f => do
      let value ← atField f host candidate fixed
      abstractAt (cal.push f) value
    synthesizeSyntheticMVarsNoPostponing
    let proof := ShareCommon.shareCommon (← instantiateMVars proof)
    let goal := ShareCommon.shareCommon (← instantiateMVars goal)
    unless !proof.hasMVar && !goal.hasMVar && !proof.hasFVar && !goal.hasFVar && !proof.hasSorry do
      throwError "unresolved original report arguments"
    let binder := mkLambda `p .default (mkSort .zero) (mkBVar 0)
    return mkAppN (Lean.mkConst ``PSigma.mk [.succ .zero,.zero]) #[mkSort .zero,binder,goal,proof]

local elab "registeredMixedReport%" : term => compileReport
private noncomputable def registeredMixedReport : PSigma (fun statement : Prop => statement) := registeredMixedReport%
end Diagonal.OriginalRegisteredMixed

namespace Diagonal
open OriginalRegisteredMixed

/-- For each original field and team, the reached report supplies its actual mixed scan, read
locations and received cells from the same registered host. -/
theorem SignedCalendarAt.mixedReportOnOriginalReports : registeredMixedReport.1 := registeredMixedReport.2
end Diagonal

end BorderVNP
end Computability
end OAI
