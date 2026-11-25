import OAI.Computability.BorderVNP.RoutingISASignedPrepBroadcast
import Lean.Elab.Term

/-! # Original calendar operands from a measured route

The route checker and the physical readback take the same calendar arguments.
The registrar also records the actual word entries and the checker for those
entries. These term elaborators reuse those recorded arguments when applying
the corresponding operation to a particular original report. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

private partial def recordedApplication (expression : Expr) : MetaM Expr := do
  let term := (← instantiateMVars expression).consumeMData.headBeta
  match term.getAppFn with
  | .const .. => return term
  | .fvar id =>
    let some value := (← id.getDecl).value? | throwError "expected a recorded calendar application"
    recordedApplication (mkAppN value term.getAppArgs)
  | _ => throwError "expected a recorded calendar operation"

private def argumentsThrough (application : Expr) (last : Name) : MetaM (Array Expr) := do
  let mut type := (← getConstInfo application.getAppFn.constName!).type
  let mut args := #[]
  for x in application.getAppArgs do
    unless type.isForall do break
    args := args.push x
    if type.bindingName! == last then return args
    type := type.bindingBody!
  throwError "no recorded calendar parameter {last} in {application.getAppFn.constName?}"

private def calendarOperation (source : Syntax) (last : Option Name) (operation : Syntax)
    (tail : Array (TSyntax `term)) : TermElabM Expr := do
  let recorded ← recordedApplication (← elabTerm source none)
  let args ← match last with
    | none => pure recorded.getAppArgs
    | some binder => argumentsThrough recorded binder
  let op ← realizeGlobalConstNoOverloadWithInfo operation
  let levels := recorded.getAppFn.constLevels!
  unless (← getConstInfo op).levelParams.length == levels.length do
    throwError "the calendar and its source operation have different universe parameters"
  let rest ← tail.mapM fun x => elabTerm x none
  return mkAppN (mkConst op levels) (args ++ rest)

/-- Apply the readback to the actual checker's calendar, pin, history, and subtotal. -/
elab "originalCheckedReadback% " source:term:max " using " op:ident " at " "[" xs:term,* "]" : term =>
  calendarOperation source none op xs.getElems

/-- Apply a source operation with the calendar operands through the named
parameter, followed by the supplied original field and team coordinates. -/
elab "originalCalibratedOperation% " source:term:max " through " last:ident
    " using " op:ident " at " "[" xs:term,* "]" : term =>
  calendarOperation source (some last.getId) op xs.getElems

private def originalArgument (application : Expr) (name : Name) : MetaM Expr := do
  let args ← argumentsThrough application name
  return args.back!

/-- Form the declaration for a pinned original route at the very arena of
this readback's selected sites. The route itself records its owner map and
team index, so these need no new inference from the ambient calendar. -/
elab "originalCheckedDeclaration% " family:term:max " at " pinned:term:max : term => do
  let sites ← elabTerm family none
  let .forallE _ declared _ _ ← whnf (← inferType sites)
    | throwError "expected the original readback's selected sites"
  let some field ← whnfUntil declared ``RoutingISA.Evaluator.SignedPrep.CheckedBroadcast
    | throwError "expected the original checked broadcast arena"
  let arena := field.getAppArgs.back!
  let route := mkProj ``Subtype 0 (← elabTerm pinned none)
  let some original ← whnfUntil (← inferType route) ``Cube.Physical.NativeAssignments.Routed
    | throwError "expected a pinned native route"
  let owners ← originalArgument original `owners
  let team ← originalArgument original `Team
  let some teams ← whnfUntil team ``Fin | throwError "expected the finite team index of an original route"
  let count := mkApp (mkConst ``Nat.pred) teams.getAppArgs.back!
  return mkAppN (← mkConstWithLevelParams ``RoutingISA.Evaluator.SignedPrep.routeBroadcast) #[count,arena,owners,route]

end Diagonal

end BorderVNP
end Computability
end OAI
