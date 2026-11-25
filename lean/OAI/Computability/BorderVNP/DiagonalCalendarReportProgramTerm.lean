import OAI.Computability.BorderVNP.DiagonalCalendarAdmittedRegisteredExecution
import OAI.Computability.BorderVNP.DiagonalCalendarClockFromOriginalRequests
import OAI.Computability.BorderVNP.DiagonalCalendarRouteInputsOnOriginalReports

/-! # Assembling the native pin at its authenticated original report inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta

/-- The original packet, cost and registration operators have the same calendar indices. Some
of them additionally need the numerical header bound immediately before the table values. -/
private def reportArity (op : Expr) (stored : Bool) : MetaM Nat := do
  let simple := if stored then 53 else 52
  forallBoundedTelescope (← inferType op) (some simple) (whnfType:=true) fun xs _ => do
    unless xs.size == simple do throwError "the operator omits an original calendar coordinate"
    let last := (← xs.back!.fvarId!.getDecl).userName.eraseMacroScopes
    if stored then
      if last == `stored then return simple
      if last == `reports || last == `replay then return simple+1
    else
      if last == `reports || last == `replay then return simple
      if last == `h then return simple+1
    throwError "unexpected original report coordinate {last}"

/-- Construct the kernel term for one native execution. Its measured time comes from these
writer requests, its sparse calls from these sites, and its registered returns from the same
measured original source. With a stored argument, all three operators see the very same family.
Sharing the resulting telescope keeps the complete dependent result practical to export. -/
def SignedCalendarAt.checkedOriginalReportProgram (siteName requestName runName : Name)
    (stored : Bool) : MetaM Expr := do
  let site ← mkConstWithLevelParams siteName
  let request ← mkConstWithLevelParams requestName
  let run ← mkConstWithLevelParams runName
  let siteSize ← reportArity site stored
  let requestSize ← reportArity request stored
  let runSize ← reportArity run stored
  let size := max siteSize (max requestSize runSize)
  let donor := if siteSize == size then site else if requestSize == size then request else run
  forallBoundedTelescope (← inferType donor) (some size) (whnfType:=true) fun xs _ => do
    let simple := if stored then 53 else 52
    let ordinary ← if size == simple then pure xs else do
      let index := size - (if stored then 5 else 4)
      unless (← inferType xs[index]!).isAppOfArity ``Fact 1 do
        throwError "the calendar header bound is missing"
      pure (xs.extract 0 index ++ xs.extract (index+1) size)
    let common := if stored then ordinary.pop else ordinary
    let select (arity : Nat) := if arity == size then xs else ordinary
    let valid := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.routeInputsOnOriginalReports) common
    let calls := mkAppN site (select siteSize)
    let requests := mkAppN request (select requestSize)
    let clock := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.clockFromOriginalRequests)
      (common.push requests)
    let registered := mkAppN run ((select runSize).push clock)
    let wired := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedExecutionAtReportedPost)
      (common.pop ++ #[valid,clock,calls,registered,requests])
    let ctx ← instantiateLCtxMVars (← getLCtx)
    let .ok result := Kernel.check (← getEnv) ctx wired
      | throwError "the original site, paid writer and source runs do not fit the selected pin"
    unless (← whnfUntil result ``ChosenReader.WiredPinExecution).isSome do
      throwError "expected a complete native wired execution"
    let (claim,program) := ShareCommon.shareCommon' (← mkForallFVars xs result, ← mkLambdaFVars xs wired)
    let level ← getLevel claim
    let sort := mkSort level
    return mkAppN (mkConst ``PSigma.mk [level.succ,level])
      #[sort,mkLambda `Result .default sort (mkBVar 0),claim,program]

end Diagonal

end BorderVNP
end Computability
end OAI
