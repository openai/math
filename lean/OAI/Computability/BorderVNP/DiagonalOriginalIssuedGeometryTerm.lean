import OAI.Computability.BorderVNP.DiagonalCandidateReportTaskImage

/-! # The issued geometry of a returned signed report

The operands of `issuedGeometryOnReport` occur in the publication, opening,
allocation and returned machine records. Recover them from those records
when applying the theorem to the installed calendar. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term in
/-- Match the machine indices of the ordinary theorem against the original
eight records in its native argument. -/
private def geometryFromReturn (publication opening team advance run alloc seed image : Expr) : MetaM Expr := do
  let head ← mkConstWithFreshMVarLevels ``issuedGeometryOnReport
  forallTelescope (← inferType head) fun xs _ => do
    let mut assigned : Std.HashMap FVarId Expr := {}
    for (name, supplied) in [(`publication,publication),(`opening,opening),(`u,team),
      (`advance,advance),(`reportRun,run),(`alloc,alloc),(`seed,seed),(`packet,image)] do
      let some input ← xs.findM? fun x => return (← x.fvarId!.getDecl).userName == name |
        throwError "missing ordinary geometry operand {name}"
      assigned := assigned.insert input.fvarId! supplied
      let template ← inferType input
      let some predicate := template.getAppFn.constName? | continue
      let some native ← whnfUntil (← inferType supplied) predicate |
        throwError "the original {name} is not a {predicate}"
      unless ← isDefEq template.getAppFn native.getAppFn do throwError "native geometry universe mismatch"
      for formal in template.getAppArgs, concrete in native.getAppArgs do
        if formal.isFVar then assigned := assigned.insert formal.fvarId! concrete
    let mut done := #[]
    for x in xs do
      let field := (← x.fvarId!.getDecl).userName
      if let some arg := assigned[x.fvarId!]? then
        done := done.push arg
      else
        let ty := (← inferType x).replaceFVars (xs.extract 0 done.size) done
        if field == `bank || field == `counts then
          let zero ← forallTelescopeReducing ty fun ys target => do
            unless target.isConstOf ``Bool do throwError "unexpected native empty bank codomain"
            mkLambdaFVars ys (Lean.mkConst ``Bool.false)
          done := done.push zero
        else if field == `startBank || field == `stride then
          let some eq ← whnfUntil ty ``Eq | throwError "expected the selected allocation equality"
          done := done.push (← mkEqRefl eq.getAppArgs[1]!)
        else
          throwError "native publication, opening and images did not recover {field}"
    return mkAppN head done

open Lean Meta Elab Term in
/-- Apply the geometry theorem to the actual publication, opening, team, control
return, report return, allocation, seed and task image at a signed report.
Its initial bank and sample functions are both constantly false. -/
elab (name := originalIssuedGeometry) "originalIssuedGeometry% " xs:ident,* : term => do
  let fields ← xs.getElems.mapM (fun x => return (← getLocalDeclFromUserName x.getId).toExpr)
  let #[publication,opening,team,advance,run,alloc,seed,image] := fields |
    throwError "expected two report records, the returned team, its physical runs, allocation, seed and task image"
  geometryFromReturn publication opening team advance run alloc seed image

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
