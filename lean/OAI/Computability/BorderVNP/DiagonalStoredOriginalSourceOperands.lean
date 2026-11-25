import OAI.Computability.BorderVNP.DiagonalFundedReportAddresses
import OAI.Computability.BorderVNP.PackedRetainedReportUse

/-! # Recovering the operands of a report collected at its original site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term RoutingISA.FragmentRows

private def originalFields (head : Name) (applied : Expr) : MetaM (NameMap Expr) := do
  let mut signature := (←getConstInfo head).type
  let mut fields : NameMap Expr := {}
  for v in applied.getAppArgs do
    let .forallE key _ rest _ := signature | throwError "unexpected original report metadata"
    fields := fields.insert key v
    signature := rest
  return fields

/-- Read the genuine original report's schema, emission, ownership and directory
from its funded subtype. The bank is the stored argument of its retained bundle.
The extra return value is the port enumeration stored on this same report. -/
def SignedCalendarAt.storedOriginalInputs (receipt : Expr) : MetaM (NameMap Expr × Expr) := do
  let d := mkProj ``Subtype 0 receipt
  let some model ← whnfUntil (←inferType d) ``EmittedReport | throwError "expected the emitted original report"
  let some native ← whnfUntil (←inferType (mkProj ``Subtype 1 receipt)) ``EmittedReport.FundedFacts |
    throwError "expected all saved facts of the same original report"
  let mut fields ← originalFields ``EmittedReport.FundedFacts native
  let schema ← originalFields ``EmittedReport model
  for key in [`E,`I,`P] do
    let some value := schema.find? key | throwError "missing original schema {key}"
    fields := fields.insert key value
  let some payload := fields.find? `payload | throwError "missing saved payload"
  let some retained ← whnfUntil payload ``Packing.DeckGrid.WiredWitness.retainedBundle |
    throwError "expected this history's retained report bundle"
  fields := fields.insert `bank retained.getAppArgs.back!
  let mut signature := (←getConstInfo ``EmittedReport).type
  for v in model.getAppArgs do
    let .forallE _ _ rest info := signature | throwError "unknown original report schema"
    if info.isInstImplicit then return (fields,v)
    signature := rest
  throwError "missing original port enumeration"

/-- Apply a field-and-team operation to a single received funded report. All
the intermediate arguments are read from that same report's type. -/
def SignedCalendarAt.payStoredOriginalReport (point receipt : Expr) : MetaM Expr := do
  let (native,port) ← storedOriginalInputs receipt
  let mut value := point
  let mut type ← inferType point
  for _ in [:45] do
    let .forallE name domain body info ← whnf type | throwError "expected the received original report"
    let key := name.eraseMacroScopes
    if key == `original then return mkApp value receipt
    let supplied := if info.isInstImplicit then some port else native.find? key
    let some x := supplied
      | if (←whnfUntil domain ``Subtype).isSome then return mkApp value receipt
        else throwError "the genuine original report has no {name} operand"
    value := mkApp value x
    type := body.instantiate1 x
  throwError "the stored original report is missing"

private def restoreOriginalSchema (point : Expr) : MetaM Expr := do
  let .forallE first _ _ _ ← whnf (←inferType point) | throwError "expected a report-paying operation"
  if first.eraseMacroScopes == `E then return point
  let applied ← if point.isFVar then pure ((←point.fvarId!.getDecl).value?.getD point) else pure point
  let args := applied.getAppArgs
  for n in [1:5] do
    if n ≤ args.size && (args.extract (args.size-n) args.size).all (fun x => x.getAppFn.isMVar) then
      let original := mkAppN applied.getAppFn (args.extract 0 (args.size - n))
      let .forallE key _ _ _ ← whnf (←inferType original) | continue
      if key.eraseMacroScopes == `E then return original
  throwError "expected the paying operation before its original report schema"

/-- Pay for the original case using the single received source at that field and team. -/
elab "payStoredOriginalReport% " point:term:max receipt:term:max : term => do
  let p ← if point.raw.isIdent then
    match (←getLCtx).findFromUserName? point.raw.getId with
    | some decl => pure decl.toExpr
    | none => elabTerm point none
  else elabTerm point none
  let original ← elabTerm receipt none
  SignedCalendarAt.payStoredOriginalReport (←restoreOriginalSchema p) original

end Diagonal

end BorderVNP
end Computability
end OAI
