import OAI.Computability.BorderVNP.DiagonalPublishedCandidateReportGeometry

/-! # Reading the original report frame from its publication, capacity and opening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- Fill the physical machine indices from the three native records themselves, stopping
at the team binder of the frame theorem. -/
private def originalFrameApplication (published capacity opened : Expr) : MetaM Expr := do
  let head ← mkConstWithFreshMVarLevels ``CandidateReportPublication.reportFrameGeometry
  forallTelescope (← inferType head) fun args _ => do
    let mut values : Std.HashMap FVarId Expr := {}
    for (name, actual) in [(`K, published), (`C, capacity), (`opening, opened)] do
      let some operand ← args.findM? fun v => return (← v.fvarId!.getDecl).userName == name |
        throwError "missing native operand {name}"
      let formalType ← inferType operand
      let some c := formalType.getAppFn.constName? | throwError "expected a native record"
      let some actualType ← whnfUntil (← inferType actual) c | throwError "operand {name} is not a {c}"
      unless ← isDefEq formalType.getAppFn actualType.getAppFn do throwError "native record universe mismatch"
      values := values.insert operand.fvarId! actual
      for formal in formalType.getAppArgs, native in actualType.getAppArgs do
        if formal.isFVar then values := values.insert formal.fvarId! native
    let mut terms := #[]
    for x in args do
      let name := (← x.fvarId!.getDecl).userName
      if name == `u then return mkAppN head terms
      let some value := values[x.fvarId!]? | throwError "native records did not specify {name}"
      terms := terms.push value
    throwError "missing original team binder"

/-- The native publication, capacity and opening keep every site and team argument of the report theorem. -/
elab (name := originalRoomFrame) "originalRoomFrame% " p:term:max c:term:max o:term:max : term => do
  originalFrameApplication (← elabTerm p none) (← elabTerm c none) (← elabTerm o none)

/-- Extract the witness to an existentially supplied native report record, with its
return coordinates taken directly from the installed frame. -/
syntax "originalReportEvidence% " term:max " at " "[" term,* "]" : term
elab_rules : term
  | `(originalReportEvidence% $family at [$[$coords],*]) => do
    let result := mkAppN (← elabTerm family none) (← coords.mapM fun coord => elabTerm coord none)
    let some info ← whnfUntil (← inferType result) ``Nonempty |
      throwError "expected a returned native report witness"
    let .const _ levels := info.getAppFn | throwError "expected Nonempty"
    return mkApp2 (mkConst ``Classical.choice levels) info.getAppArgs.back! result

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
