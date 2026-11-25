import OAI.Computability.BorderVNP.DiagonalRegisteredNativeReportGeometry
import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerReportGeometryInputs

/-! # Geometry on the calendar's original returned candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- Read matching parameters at the head of a retained native certificate. -/
private def certificateFields (formal actual : Expr) : MetaM (Array (Expr × Expr)) := do
  let head := (← inferType formal).getAppFn.constName!
  let some registered ← whnfUntil (← inferType actual) head
    | throwError "expected the source certificate {head}"
  let pattern := (← inferType formal).getAppArgs
  return Array.zip pattern registered.getAppArgs

/-- Supply the native report theorem with precisely the parameters recorded
by the returned candidate and its original allocated source. -/
elab "nativeGeometryAtIssuedReport% " C:term:max visit:term:max team:term:max atSite:term:max
    complete:term:max caps:term:max seed:term:max allocation:term:max : term => do
  let actual ← elabTerm C none
  let U ← elabTerm (← `(attainedStarts% $visit)) none
  let active ← elabTerm (← `(attainedPrefix% $visit)) none
  let same ← elabTerm visit none
  let some eq ← whnfUntil (← inferType same) ``Eq | throwError "expected the original owner equality"
  let some owns ← whnfUntil eq.getAppArgs[1]! ``PinStart.ownedVisits |
    throwError "expected the concrete native prefix"
  let n ← forallTelescope (← getConstInfo ``PinStart.ownedVisits).type fun ps _ => do
    for (p,i) in ps.zipIdx do if (← p.fvarId!.getUserName)==`n then return owns.getAppArgs[i]!
    throwError "expected the original input length"
  let e ← elabTerm seed none
  let a ← elabTerm allocation none
  let method := ``ReturnedCandidateReports.reportGeometryOnOriginalVisits
  let signature ← getConstInfo method
  let supplied : List (Name × Expr) := [(`U,U),(`active,active),(`n,n),(`u,← elabTerm team none),
    (`actual,actual),(`located,← elabTerm atSite none),(`complete,← elabTerm complete none),(`caps,← elabTerm caps none),
    (`seed,e),(`alloc,a),(`suffix,mkNatLit 0)]
  forallTelescope signature.type fun params _ => do
    let names ← params.mapM fun p => p.fvarId!.getUserName
    let mut fields := #[]
    for (name,witness) in [(`actual,actual),(`seed,e),(`alloc,a)] do
      let some i := names.idxOf? name | throwError "missing registered input {name}"
      fields := fields ++ (← certificateFields params[i]! witness)
    let mut args := #[]
    for (x,i) in params.zipIdx do
      let name := names[i]!
      if let some value := supplied.lookup name then
        args := args.push value
      else if let some pair := fields.find? (fun pair => pair.1==x) then
        args := args.push pair.2
      else if [`pubAt,`owned,`bankAt].contains name then
        let e := (← inferType x).replaceFVars (params.extract 0 i) args
        let some identity ← whnfUntil e ``Eq | throwError "expected native address identity {name}"
        args := args.push (← mkEqRefl identity.getAppArgs[1]!)
      else throwError "unfilled original native operand {name}"
    let some registered ← whnfUntil (← inferType actual) ``ReturnedCandidateReports | throwError "expected original C"
    let universes := registered.getAppFn.constLevels!
    unless universes.length == signature.levelParams.length do
      throwError "the original candidate and native geometry have different universe arities"
    return mkAppN (mkConst method universes) args

end RoutingISA.Evaluator.SignedPrep

namespace Diagonal
open Lean Meta

/-- Recover the original field's geometry arguments from its actual native
residence, site, and stage. Every additional size or memory is an index of
one of those three records. -/
private def SignedCalendarAt.fragmentOnNativeCandidate (task routing u held site attained : Expr) : MetaM Expr := do
  let fn := ``SignedCalendarAt.frozenPlannerReportGeometryInputs
  let some fixed ← whnfUntil task ``SignedCalendarAt.frozenPlannerTask | throwError "expected the original signed planner"
  let info ← getConstInfo fn
  forallTelescope info.type fun params _ => do
    let names ← params.mapM fun p => p.fvarId!.getUserName
    let supplied : List (Name × Expr) := [(`held,held),(`site,site),(`attained,attained)]
    let mut fields := #[]
    let mut levels : NameMap Level := {}
    for (name,value) in supplied do
      let some index := names.idxOf? name | throwError "missing native field {name}"
      let pattern ← inferType params[index]!
      let head := pattern.getAppFn.constName!
      let some data ← whnfUntil (← inferType value) head |
        throwError "expected native record {head}"
      for (formal,actual) in pattern.getAppFn.constLevels!.zip data.getAppFn.constLevels! do
        if let .param name := formal then levels := levels.insert name actual
      let indexes := Array.zip pattern.getAppArgs data.getAppArgs
      fields := fields ++ indexes
      for (original,registered) in indexes do
        if original.getAppFn.isConstOf ``List.ofFn then
          let some row ← whnfUntil registered ``List.ofFn | throwError "expected the original profile word"
          fields := fields ++ Array.zip original.getAppArgs row.getAppArgs
    let mut args := fixed.getAppArgs ++ #[routing,u]
    unless names[args.size]! == `copy do throwError "unexpected first native geometry operand {names[args.size]!}"
    for x in params.extract args.size params.size do
      let n ← x.fvarId!.getUserName
      if let some v := supplied.lookup n then
        args := args.push v
      else if let some pair := fields.find? (fun pair => pair.1==x) then
        args := args.push pair.2
      else throwError "unfilled native geometry operand {n}"
    let universes ← info.levelParams.mapM fun name => do
      let some level := levels.find? name | throwError "missing universe of native geometry field {name}"
      return level
    return mkAppN (mkConst fn universes) args

end Diagonal

namespace Diagonal
open Lean Meta Elab Term TeamContraction RoutingISA RoutingISA.Evaluator SignedPrep
set_option maxRecDepth 22000
set_option maxHeartbeats 16000000
set_option cleanup.letToHave false
private def byName (xs : Array Expr) (n : Name) : MetaM Expr := do
  let some x ← xs.findM? (fun x => return (← x.fvarId!.getUserName) == n)
    | throwError "missing original calendar argument {n}"
  return x

private def namedArgument (spine : Expr) (n : Name) : MetaM Expr := do
  let info ← getConstInfo spine.getAppFn.constName!
  let mut type := info.type
  for x in spine.getAppArgs do
    if type.bindingName! == n then return x
    type := type.bindingBody!
  throwError "missing argument {n} in {info.name}"

private def actualCandidate (report : Expr) : MetaM Expr := do
  let mut result := report
  for _ in [0:2] do
    let some spec ← whnfUntil (← inferType result) ``Exists | throwError "expected attained candidate coordinates"
    result := mkAppN (mkConst ``Classical.choose_spec spec.getAppFn.constLevels!) (spec.getAppArgs.push result)
  let some box ← whnfUntil (← inferType result) ``Nonempty | throwError "expected the returned candidate"
  return mkAppN (mkConst ``Classical.choice box.getAppFn.constLevels!) (box.getAppArgs.push result)


private def certificateAt (inputs : Array Expr) (u actual reached : Expr) : TermElabM Expr := do
  let some returned ← whnfUntil (← inferType actual) ``ReturnedCandidateReports |
    throwError "expected the native candidate at the true return"
  let sites ← namedArgument returned `site
  let some site ← whnfUntil (mkApp sites u) ``PreparationFrame.SelectedLookupSites.returnedSite |
    throwError "expected the candidate's original observed site"
  let stages := mkAppN (mkConst ``PreparationFrame.SelectedLookupSites.returnedSiteStages site.getAppFn.constLevels!) site.getAppArgs
  let lifetime := mkProj ``And 0 stages
  let some ex ← whnfUntil (← inferType lifetime) ``Exists | throwError "missing the attained native site stages"
  let issued := mkAppN (mkConst ``Classical.choose_spec ex.getAppFn.constLevels!) (ex.getAppArgs.push lifetime)
  let retained := mkProj ``And 0 issued
  let boot := mkProj ``And 0 (mkProj ``And 1 (mkProj ``And 1 (mkProj ``And 1 issued)))
  let cal ← exprToSyntax (← byName inputs `cal)
  let op ← byName inputs `oper
  let grid ← exprToSyntax (← mkProjection op `grid)
  let routing ← mkProjection op `routing
  let qpos ← exprToSyntax (← byName inputs `qpos)
  let pos ← exprToSyntax (← byName inputs `position)
  let chart ← exprToSyntax (← byName inputs `chart)
  let reader ← exprToSyntax (← byName inputs `reader)
  let charge ← exprToSyntax (← byName inputs `chargeFit)
  let team ← exprToSyntax u
  let task ← elabTerm (← `(($cal).frozenPlannerTask $grid $qpos $pos $chart $reader $charge)) none
  synthesizeSyntheticMVarsNoPostponing
  let fragment ← SignedCalendarAt.fragmentOnNativeCandidate task routing u boot site retained
  withLetDecl `returnedGeometry (← inferType fragment) fragment fun geom => do
    let loc ← exprToSyntax (mkProj ``And 0 geom)
    let complete ← exprToSyntax (mkProj ``And 0 (mkProj ``And 1 geom))
    let caps ← exprToSyntax (mkProj ``And 1 (mkProj ``And 1 geom))
    let c ← exprToSyntax actual
    let same ← exprToSyntax reached
    let receipt ← elabTerm (← `(preparedOnAttainedOwner% $c $same $team)) none
    let alloc ← exprToSyntax receipt
    let proof ← elabTerm (← `(nativeGeometryAtIssuedReport% $c $same $team $loc $complete $caps
      (($alloc).2.source_seed ($alloc).1.1) (($alloc).2.source_allocation ($alloc).1.2))) none
    mkLetFVars #[geom] proof

/-- Instantiate the native report geometry at every field and receiving team of
a calendar's returned-candidate theorem. Its result includes the attained
equality with the original owner visits. -/
def SignedCalendarAt.geometryOnCandidateFields (candidate : Name) : MetaM Expr := do
  let constant ← mkConstWithLevelParams candidate
  let type ← inferType constant
  forallBoundedTelescope type (some type.getForallArity) fun inputs _ => do
    let family := mkAppN constant inputs
    let .forallE _ field _ _ ← whnf (← inferType family) | throwError "expected the original field"
    let proof ← withLocalDeclD `f field fun f => do
      let source := mkApp family f
      let actual ← actualCandidate (mkProj ``And 0 source)
      let reached := mkProj ``And 1 source
      let some report ← whnfUntil (← inferType actual) ``ReturnedCandidateReports |
        throwError "expected the candidate's native report"
      let sites ← namedArgument report `site
      let .forallE _ teams _ _ ← whnf (← inferType sites) | throwError "expected the registered teams"
      withLocalDeclD `u teams fun u => do
        let atTeam ← TermElabM.run' (certificateAt inputs u actual reached)
        mkLambdaFVars #[f,u] atTeam
    mkLambdaFVars inputs proof

end Diagonal

end BorderVNP
end Computability
end OAI
