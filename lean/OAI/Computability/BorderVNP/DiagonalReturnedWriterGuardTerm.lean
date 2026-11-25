import OAI.Computability.BorderVNP.DiagonalReturnedWriterChecks

/-! # Reading the two native guards from the observed signed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction.ProcessorSlots

/-- Match the parameters observable directly in the boot and signed scan.
Larger computed expressions in these types are already specified by those
parameters, so the application needs no search for them. -/
private def scanFields (model actual : Expr) : Array (FVarId × Expr) :=
  (model.getAppArgs.zip actual.getAppArgs).filterMap fun (p,v) =>
    if p.isFVar then some (p.fvarId!,v) else none

private def writerHead (stated : Expr) (name : Name) : MetaM Expr := do
  let some head ← whnfUntil stated name | throwError "expected a physical {name}"
  return head

private def levelPairs (model actual : Expr) : List (Name × Level) :=
  (model.getAppFn.constLevels!.zip actual.getAppFn.constLevels!).filterMap fun (lhs,rhs) =>
    match lhs with
    | .param n => some (n,rhs)
    | _ => none

/-- Apply the two native guard checks using the indices carried by the
actual returned writer and its originating boot. The operands are the
entry identifier, boot, guess, profile, proof of its spelling, observed
scan, positive header width, returned prefix and agreement on the guess. -/
syntax (name := returnedWriterGuard) "returnedWriterGuard% " term:max term:max term:max term:max term:max term:max
  term:max term:max term:max : term

elab_rules : term
  | `(returnedWriterGuard% $id $boot $g $prof $spelling $observed $hd $pfx $chosen) => do
    let caller ← getLCtx
    let callerInstances ← getLocalInstances
    let explicitInput (arg : Syntax) (expected : Option Expr) : TermElabM Expr :=
      withLCtx caller callerInstances (elabTerm arg expected)
    let node ← explicitInput boot none
    let source ← explicitInput observed none
    let nodeType ← writerHead (← inferType node) ``BootedPinStart
    let sourceType ← writerHead (← inferType source) ``ReturnedWriterScan
    let decl ← getConstInfo ``BootedPinStart.published_returned_scan_checks
    forallTelescope decl.type fun ps _ => do
      let mut fields := #[]
      let mut universes := []
      for param in ps do
        let name ← param.fvarId!.getUserName
        if name == `B || name == `source then
          let actual := if name == `B then nodeType else sourceType
          let model ← writerHead (← inferType param) actual.getAppFn.constName?.get!
          fields := fields ++ scanFields model actual
          universes := levelPairs model actual ++ universes
      let levels ← decl.levelParams.mapM fun n => do
        let some (_,u) := universes.find? (·.1 == n)
          | throwError "the returned scan does not determine universe {n}"
        return u
      let mut op := Lean.mkConst decl.name levels
      let mut ty ← inferType op
      for param in ps do
        let name ← param.fvarId!.getUserName
        let dom := ty.bindingDomain!
        let value ← match name with
          | `B => pure node
          | `source => pure source
          | `id => explicitInput id none
          | `g => explicitInput g none
          | `profile => explicitInput prof none
          | `spelling => explicitInput spelling (some dom)
          | `hd => explicitInput hd none
          | `code => explicitInput pfx none
          | `chosen => explicitInput chosen none
          | _ => do
            let some (_,v) := fields.find? (·.1 == param.fvarId!)
              | throwError "the returned writer leaves input {name} undetermined"
            pure v
        op := mkApp op value
        ty := ty.bindingBody!.instantiate1 value
      return op

end Diagonal

end BorderVNP
end Computability
end OAI
