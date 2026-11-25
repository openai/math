import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldGeometry
import OAI.Computability.BorderVNP.DiagonalCalendarPacketHostEntry
import OAI.Computability.BorderVNP.DiagonalIssuedHostProgramTerm
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-! # The registered host directory on an original issued field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction RoutingISA RoutingISA.Evaluator SignedPrep
open private serviceAt from OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldGeometry

private def parameter (xs : Array Expr) (name : Name) : MetaM Expr := do
  let some x ← xs.findM? (fun x => return (← x.fvarId!.getUserName) == name)
    | throwError "missing original calendar argument {name}"
  return x

private def argument (application : Expr) (name : Name) : MetaM Expr := do
  let mut signature := (← getConstInfo application.getAppFn.constName!).type
  for value in application.getAppArgs do
    let .forallE binder _ body _ := signature | throwError "unexpected calendar argument"
    if binder == name then return value
    signature := body
  throwError "missing {name} on the original returned field"

private def readerOnHistory (inputs : Array Expr) (history : Expr) : MetaM Expr := do
  let operation := ``SignedCalendarAt.frozenHostProgramEntry
  let info ← getConstInfo operation
  let oper ← parameter inputs `oper
  let mut signature := info.type
  let mut args := #[]
  while signature.isForall do
    let key := signature.bindingName!
    let value ← if key == `grid || key == `routing then mkProjection oper key
      else if key == `hist then pure history
      else if signature.bindingInfo!.isInstImplicit then synthInstance (signature.bindingDomain!.instantiateRev args)
      else parameter inputs key
    args := args.push value
    if key == `hist then return mkAppN (mkConst operation (info.levelParams.map fun _ => Level.zero)) args
    signature := signature.bindingBody!
  throwError "expected the issuing reader at the original history"

set_option maxRecDepth 22000 in
set_option maxHeartbeats 22000000 in
private def entryOnSelectedGeometry : TermElabM Expr := do
  let geometry ← mkConstWithLevelParams ``SignedCalendarAt.registeredPhysicalOnOriginalSelection
  forallTelescopeReducing (← inferType geometry) fun inputs _ => do
    let field := inputs[inputs.size-3]!
    let selection := inputs[inputs.size-2]!
    let team := inputs.back!
    let valid ← parameter inputs `valid
    let owner := mkApp (← serviceAt valid ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates) field
    let some received ← whnfUntil (← inferType owner) ``PreparationFrame.ReturnedOwnershipAt |
      throwError "expected the field's original returned ownership"
    let exterior ← argument received `origin
    let some visits ← whnfUntil (← argument received `run) ``PinStart.ownedVisits |
      throwError "expected the original team's preparations"
    let starts ← argument visits `S
    let bank ← exprToSyntax (← mkProjection (mkApp starts team) `pub)
    let chosen ← exprToSyntax selection
    let sites ← elabTerm (← `((originalLookupSites% $chosen))) none
    let site := mkAppN sites #[exterior,team]
    let epoch ← exprToSyntax (← mkProjection site `epoch)
    let published ← exprToSyntax (← mkProjection site `published)
    let memory ← exprToSyntax (← mkProjection site `epochMemory)
    let physical := mkProj ``And 0 (mkAppN geometry inputs)
    let stored := mkProj ``And 1 physical
    let packet ← exprToSyntax (mkProj ``And 0 stored)
    let pin ← exprToSyntax (mkProj ``And 1 stored)
    let hist := mkProj ``Sigma 0 (mkProj ``Sigma 1 field)
    let reader ← exprToSyntax (← readerOnHistory inputs hist)
    let entry ← elabTerm (← `(issuedHostProgramOn% $reader $bank $pin $epoch $published $memory $packet)) none
    mkLambdaFVars inputs entry

local elab "originalFieldCanonicalEntry%" : term => entryOnSelectedGeometry

set_option maxRecDepth 22000 in
set_option maxHeartbeats 22000000 in
set_option cleanup.letToHave false in
private noncomputable def originalHostDirectory : PSigma fun statement : Prop => statement :=
  ⟨_, originalFieldCanonicalEntry%⟩

/-- On every original field, the selected team's native epochs publish the canonical
directory. Its slotted writer and its report-word conversion use that same middle
memory and the public operand of the originally prepared team. -/
theorem SignedCalendarAt.canonicalEntryOnOriginalSelection : originalHostDirectory.1 :=
  originalHostDirectory.2

end Diagonal

end BorderVNP
end Computability
end OAI
