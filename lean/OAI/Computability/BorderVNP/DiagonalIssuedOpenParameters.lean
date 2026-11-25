import OAI.Computability.BorderVNP.DiagonalReturnedFundedOpen

/-! # The header and dictionary width of the returned signed opener -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

private def issuedOpenParameter (operand : Syntax) (parameter : Name) : TermElabM Expr := do
  let opened ← elabTerm operand none
  let some ty ← whnfUntil (← inferType opened) ``IssuedOpenOperands
    | throwErrorAt operand "expected the operands of the returned signed opener"
  let declaration ← getConstInfo ``IssuedOpenOperands
  forallTelescope declaration.type fun fields _ => do
    for field in fields, value in ty.getAppArgs do
      if (← field.fvarId!.getUserName) == parameter then
        return value
    throwError "missing parameter {parameter} of the returned signed opener"

/-- Read the actual original bundle-header function used by the opener's placement and readiness proofs. -/
elab "issuedOpenHeader%" opened:term : term => issuedOpenParameter opened `hdr

/-- Read the actual dictionary width whose power of two bounds the opener's room. -/
elab "issuedOpenBits%" opened:term : term => issuedOpenParameter opened `bits

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
