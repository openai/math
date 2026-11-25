import OAI.Computability.BorderVNP.DiagonalCalendarCandidateEmissionInputs

/-! # The emission operands stored in an original candidate return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term

/-- Locate a parameter of the usual emission theorem in the corresponding
native record. The profile is stored in the inner `List.ofFn` argument. -/
private def recordedArgument (v : Expr) (patterns actual : Array Expr) : MetaM Expr := do
  for (p,j) in patterns.zipIdx do
    if let some atArg := p.getAppArgs.idxOf? v then
      return actual[j]!.getAppArgs[atArg]!
  for (p,j) in patterns.zipIdx do
    for (nested,i) in p.getAppArgs.zipIdx do
      if let some k := nested.getAppArgs.idxOf? v then
        let .const head _ := nested.getAppFn | throwError "expected a recorded field application"
        let field := actual[j]!.getAppArgs[i]!
        let some original ← whnfUntil field head | throwError "expected the recorded field {head}"
        return original.getAppArgs[k]!
  throwError "parameter {v} is absent from the three recorded inputs"

private def recordedEmission (head u held site attained : Expr) : MetaM Expr := do
  let prec ← getConstInfo ``SignedCalendarAt.frozenCandidateEmissionInputs
  let tail ← forallTelescope prec.type fun binders _ => do
    let labels ← binders.mapM fun v => do pure (← getFVarLocalDecl v).userName
    let index (n : Name) : MetaM Nat := do
      let some i := labels.idxOf? n | throwError "expected emission parameter {n}"
      return i
    let start ← index `u
    let positions ← #[`held,`site,`attained].mapM index
    let supplied := #[held,site,attained]
    let patterns ← positions.mapM fun i => inferType binders[i]!
    let actual ← (patterns.zip supplied).mapM fun (pattern,term) => do
      let .const name _ := pattern.getAppFn | throwError "expected a native record type"
      let some native ← whnfUntil (← inferType term) name | throwError "expected the native record {name}"
      return native
    -- The host, port and operand universes are fixed by the stored site.
    let .const callee levels := head.consumeMData.getAppFn | throwError "expected the usual partially applied emission proof"
    unless callee == prec.name do throwError "expected the native emission theorem"
    for (pattern,native) in patterns.zip actual do
      for (symbol,level) in pattern.getAppFn.constLevels!.zip native.getAppFn.constLevels! do
        let expected := symbol.instantiateParams prec.levelParams levels
        unless ← isDefEq (mkSort expected) (mkSort level) do throwError "incompatible native input universe"
    let mut args := #[]
    for i in [start+1:binders.size] do
      if let some j := positions.idxOf? i then
        args := args.push supplied[j]!
      else
        args := args.push (← recordedArgument binders[i]! patterns actual)
    return args
  return mkAppN (mkApp head u) tail

/-- Apply the usual emission proof at a selected held state, site, and return. -/
elab (name := emissionOnOriginal) "emissionOnOriginal% " head:term "," u:term "," held:term "," site:term "," attained:term : term => do
  recordedEmission (← elabTerm head none) (← elabTerm u none) (← elabTerm held none)
    (← elabTerm site none) (← elabTerm attained none)

end Diagonal

end BorderVNP
end Computability
end OAI
