import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved
import OAI.Computability.BorderVNP.DiagonalReturnedFundedOpen

/-! # Issued report operands on the attained physical owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep
open Lean Meta Elab Term CompactMachine

/-- Read the exact starts, active prefix and native input length carried in the
left hand side of the attained physical owner equality. -/
private def originalOwner (attained : Expr) : MetaM (Expr × Expr × Expr) := do
  let some equality ← whnfUntil (← inferType attained) ``Eq |
    throwError "expected the attained equality of owner histories"
  let some owned ← whnfUntil equality.getAppArgs[1]! ``PinStart.ownedVisits |
    throwError "expected the original physical visits on the left hand side"
  let arguments := owned.getAppArgs
  let signature ← getConstInfo ``PinStart.ownedVisits
  forallTelescope signature.type fun params _ => do
    let names ← params.mapM fun p => p.fvarId!.getUserName
    let some n := names.idxOf? `n | throwError "missing the original input length"
    unless names.back! == `p && names[names.size-2]! == `S do
      throwError "expected the original starts and their active prefix"
    return (arguments[arguments.size-2]!,arguments.back!,arguments[n]!)

/-- The family of native pin starts recorded on the left of the attained
owner equality. -/
elab (name := attainedStarts) "attainedStarts% " atVisit:term:max : term => do
  let (starts,_,_) ← originalOwner (← elabTerm atVisit none)
  return starts

/-- The joint prefix of those same native starts, before the team's
control and report returns. -/
elab (name := attainedPrefix) "attainedPrefix% " atVisit:term:max : term => do
  let (_,reached,_) ← originalOwner (← elabTerm atVisit none)
  return reached

/-- Fill the native report theorem using identical retained report fields and
the attained execution that supplies the program's owning visit. -/
private def atAttainedOwner (method : Name) (candidate atVisit team : Syntax)
    (additional : List (Name × Syntax)) : TermElabM Expr := do
  let actual ← elabTerm candidate none
  let (U,active,n) ← originalOwner (← elabTerm atVisit none)
  let u ← elabTerm team none
  let some received ← whnfUntil (← inferType actual) ``ReturnedCandidateReports |
    throwError "expected the original returned candidate reports"
  let observed := received.getAppArgs
  let supplied ← additional.mapM fun (name,term) => do return (name, ← elabTerm term none)
  let signature ← getConstInfo method
  forallTelescope signature.type fun params _ => do
    let names ← params.mapM fun x => x.fvarId!.getUserName
    let some c := names.idxOf? `actual | throwError "missing the original returned reports"
    let some pattern ← whnfUntil (← inferType params[c]!) ``ReturnedCandidateReports |
      throwError "expected the original returned report in this theorem"
    let formal := pattern.getAppArgs
    let explicit : List (Name × Expr) := [(`actual,actual),(`U,U),(`active,active),(`n,n),(`u,u)] ++ supplied
    let arguments ← params.mapM fun x => do
      let name ← x.fvarId!.getUserName
      if let some value := explicit.lookup name then return value
      let some pos := formal.findIdx? (· == x) | throwError "missing original proof parameter {name}"
      return observed[pos]!
    return mkAppN (mkConst method received.getAppFn.constLevels!) arguments

/-- Use the supplied geometry packet on the same retained candidate. -/
elab (name := issuedOnAttainedOwner) "issuedOnAttainedOwner% " C:term:max atVisit:term:max u:term:max packet:term:max : term =>
  atAttainedOwner ``ReturnedCandidateReports.issuedGeometryAtOwnPacket C atVisit u [(`packet,packet)]

/-- The open operands recorded on the owning team's physical dispatch. -/
elab (name := openedOnAttainedOwner) "openedOnAttainedOwner% " C:term:max atVisit:term:max u:term:max : term =>
  atAttainedOwner ``ReturnedCandidateReports.openOperandsAtOwnDispatch C atVisit u []

/-- Recover the prepared scanner, allocation and routed row agreement for the
same team at the control return of its attained owner prefix. -/
elab (name := preparedOnAttainedOwner) "preparedOnAttainedOwner% " C:term:max atVisit:term:max u:term:max : term =>
  atAttainedOwner ``ReturnedCandidateReports.preparedOriginalRows C atVisit u []

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
