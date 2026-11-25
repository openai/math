import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerPostOperands
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerMeanOwner
import OAI.Computability.BorderVNP.DiagonalEmittedWriterPost

/-! # The registered native report operation at each original issued point -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.FragmentRows Cube.Physical TeamContraction

private def recordedNames (applied : Expr) : MetaM (NameMap Expr) := do
  let some head := applied.getAppFn.constName? | throwError "expected a named native report operand"
  let mut signature := (← getConstInfo head).type
  let mut args : NameMap Expr := {}
  let mut inst : Nat := 0
  for x in applied.getAppArgs do
    let .forallE name _ rest info := signature | throwError "unexpected extra operand of {head}"
    let key := if info.isInstImplicit then Name.num `inventory inst else name
    if info.isInstImplicit then inst := inst+1
    args := args.insert key x
    signature := rest
  return args

private def readNative (e : Expr) (head : Name) : MetaM (NameMap Expr) := do
  let some applied ← whnfUntil e head | throwError "expected {head} on the issued return"
  recordedNames applied

private def named (r : NameMap Expr) (field : Name) : MetaM Expr := do
  let some x := r.find? field | throwError "missing native return operand {field}"
  return x


/-- Retain the input’s report and proof operands in their genuine dependent order.
The original issuer has already determined every routing and geometry parameter. -/
private partial def payReport (op : Expr) (type : Expr) (fields : NameMap Expr)
    (transfer : Expr) (args : Array Expr := #[]) (inst : Nat := 0) : MetaM Expr := do
  let .forallE name domain body info := type | return mkApp transfer (mkAppN op args)
  let key := if info.isInstImplicit then Name.num `inventory inst else name
  let next := if info.isInstImplicit then inst+1 else inst
  if let some x := fields.find? key then
    return ← payReport op body fields transfer (args.push x) next
  unless [`E,`I,`P,Name.num `inventory 0,`J,`d,`coordinates,`window,`layout,
      `directory,`marked,`geometry,`controls,`source].contains key do
    throwError "missing installed operand for the original field: {key}"
  withLocalDecl name info (domain.instantiateRev args) fun x => do
    let paid ← payReport op body fields transfer (args.push x) next
    mkLambdaFVars #[x] paid

/-- Fill the native ownership, source frame, semantic transaction and greedy owner
from the same restored field. Leave only the genuine emission and its data to be read. -/
private def onIssuedPoint (record ownership assignment : Expr) : MetaM Expr := do
  let request := mkProj ``Subtype 0 record
  let h := mkProj ``Subtype 1 record
  let transfer := mkProj ``And 0 (mkProj ``And 1 h)
  let mut values ← readNative (← inferType request) ``WriterPostRequest
  let owner ← readNative (← inferType ownership) ``PreparationFrame.ReturnedOwnershipAt
  let some rhs ← whnfUntil (← inferType assignment) ``Eq | throwError "expected the actual owner equality"
  let greedy ← readNative rhs.getAppArgs[2]! ``greedyOwner
  for (target, actual) in [(`wire,`L),(`common,`header),(`publicAt,`pub),(`macroAt,`mac),
        (`regsAt,`reg),(`memAt,`mem),(`origin,`origin),(`proto,`template₀),(`amount,`count),
        (`decl₀,`decl),(`F₀,`F),(`actualOwner,`owners),(`route₀,`v)] do
    values := values.insert target (← named owner actual)
  for (target, actual) in [(`labels,`label),(`receiver,`recv),(`widths,`dataWidth),
        (`A,`A),(Name.num `inventory 1,Name.num `inventory 0)] do
    values := values.insert target (← named greedy actual)
  values := values.insert `request request |>.insert `owned ownership |>.insert `ownerEq assignment
  let op ← mkConstWithLevelParams ``WriterPostRequest.finishRegisteredEmission
  payReport op (← inferType op) values transfer

/-- Reuse the literal eligible-source telescope. The pin, history, old selected
frame, and public terms in the resulting proof are those of this very issuer. -/
private def fundedReportOnField : MetaM Expr := do
  let .defnInfo source ← getConstInfo ``SignedCalendarAt.FrozenOriginalOwnerStatement
    | throwError "expected the original calendar’s registered ownership statement"
  forallTelescope source.value fun xs _ => do
    let some v ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the original source tables"
    let f := xs.back!
    let original := xs.pop
    let beforeRate := original.pop
    let producer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedPlannerPostOperands) beforeRate
    let .forallE r rateDomain _ _ ← whnf (← inferType producer) | throwError "expected the physical post rate"
    unless r == `rate do throwError "expected rate, found {r}"
    withLocalDeclD r rateDomain fun rate => do
      let issue := mkAppN producer #[rate,original.back!,f]
      let .forallE _ team _ _ ← whnf (← inferType issue) | throwError "expected a receiving team"
      withLocalDeclD `u team fun u => do
        let record := mkApp issue u
        let owned := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates) xs
        let hist := mkProj ``Sigma 0 (mkProj ``Sigma 1 f)
        let mean := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites_plannerMeanOwner)
          ((xs.extract 0 (v+1)).push hist)
        let paid ← onIssuedPoint record owned mean
        mkLambdaFVars (beforeRate ++ #[rate,original.back!,f,u]) paid

set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000

local elab "originalReportChargeFamily%" : term => do inferType (← fundedReportOnField)

/-- The exact native charged report operator over every original field in the restored roster. -/
abbrev SignedCalendarAt.FundedOperationOnOriginal : Prop := originalReportChargeFamily%

/-- At every such field and team the real returned owner and installed planner
charge the saved report with its source-carrying publications and matching paid window. -/
theorem SignedCalendarAt.chargeReportOnOriginal : SignedCalendarAt.FundedOperationOnOriginal := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← fundedReportOnField)
    Lean.Elab.Tactic.replaceMainGoal []


end Diagonal

end BorderVNP
end Computability
end OAI
