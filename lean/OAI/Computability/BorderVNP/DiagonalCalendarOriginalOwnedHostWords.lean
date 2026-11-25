import OAI.Computability.BorderVNP.DiagonalCalendarOwnedHostWordsType
import OAI.Computability.BorderVNP.DiagonalCalendarBareReportAssignments
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved

/-! # The joint host reading on every original calendar field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction TeamContraction.ProcessorSlots RoutingISA.Evaluator

private def operandMap (e : Expr) : MetaM (Std.HashMap Name Expr) := do
  let some name := e.getAppFn.constName? | throwError "expected a native routing declaration"
  let args := e.getAppArgs
  forallBoundedTelescope (← getConstInfo name).type (some args.size) fun formals _ => do
    let mut map : Std.HashMap Name Expr := {}
    for formal in formals, arg in args do
      map := map.insert (← formal.fvarId!.getDecl).userName.eraseMacroScopes arg
    return map

private def originalProjection (e : Expr) (field : Nat) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  let some name := ty.getAppFn.constName? | throwError "expected a native field tuple"
  return mkProj name field e

/-- Read the physical start and the entire prefix tuple from the already checked calendar
report family. Its report at one team determines the starting program at that team. -/
private def originalJointSource : MetaM Expr := do
  let .defnInfo registered ← getConstInfo ``SignedCalendarAt.OriginalBareReturnType
    | throwError "expected the original calendar report type"
  forallTelescope registered.value fun xs result => do
    let some bare ← whnfUntil result ``BootedPinStart.BareAssignmentReturns
      | throwError "expected the original field's report rows"
    let inputs ← operandMap bare
    let some lifted ← whnfUntil bare ``PLift | throwError "expected the chronological report family"
    let some valueAt ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "the original report family must specify its source matrices"
    forallBoundedTelescope lifted.appArg! (some 2) fun fu report => do
      let f := fu[0]!
      let u := fu[1]!
      let source := match report.consumeMData with
        | .letE _ _ val body _ => body.instantiate1 val
        | other => other
      let some tuple := source.find? (fun e =>
          e.isAppOf ``BootedPinStart.routedBareTuple && e.containsFVar f.fvarId!)
        | throwError "the acquired report must visit the original routed tuple"
      let some start := source.find? (fun e =>
          e.isAppOf ``BootedPinStart.start && e.containsFVar u.fvarId! && e.containsFVar f.fvarId!)
        | throwError "the acquired report must have the original team's native start"
      let starts ← mkLambdaFVars #[u] start
      let active ← originalProjection tuple 1
      let ctor := ``PinStart.ownedVisits
      let owned ← forallTelescope (← getConstInfo ctor).type fun binders _ => do
        let args ← binders.mapM fun x => do
          let k := (← x.fvarId!.getDecl).userName.eraseMacroScopes
          if k == `S then return starts
          if k == `p then return active
          let some a := inputs.get? k | throwError "missing native owner argument {k}"
          return a
        return mkAppN (← mkConstWithLevelParams ctor) args
      let pin ← originalProjection f 0
      let rest ← originalProjection f 1
      let history ← originalProjection rest 0
      let route ← originalProjection (← originalProjection (← originalProjection rest 1) 0) 0
      let fixedArgs := xs.extract 0 (valueAt+1)
      let words := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.OwnedHostWords)
        (fixedArgs ++ #[history,route,pin,owned])
      let family ← mkLambdaFVars xs (← mkForallFVars #[f] words)
      if family.hasFVar then throwError "the original joint source must be independent of the chosen report team"
      return family

local elab "originalJointSource%" : term => originalJointSource

/-- The original joint host state on each full field contains its W-selected source bits. -/
noncomputable abbrev SignedCalendarAt.OriginalOwnedHostWords := originalJointSource%

end Diagonal

end BorderVNP
end Computability
end OAI
