import OAI.Computability.BorderVNP.DiagonalCalendarLookupOwnerReadback
import OAI.Computability.BorderVNP.DiagonalCalendarCanonicalReportSource

/-! # The owner allocation of the selected writer and the published report source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction

/-- Recover the source published at the actual issuing teams' addresses. This uses the
same calendar as the lookup, projecting its execution grid and retaining its history. -/
private def publishedLookupSource (inputs : Array Expr) : MetaM Expr := do
  let mut byName : NameMap Expr := {}
  for arg in inputs do
    byName := byName.insert (← arg.fvarId!.getUserName) arg
  let some oper := byName.find? `oper | throwError "missing the calendar execution"
  let some execution ← whnfUntil (← inferType oper) ``FrozenExecutionAt
    | throwError "expected the attained calendar's execution"
  let grid := mkAppN (mkConst ``FrozenExecutionAt.grid execution.getAppFn.constLevels!) (execution.getAppArgs.push oper)
  byName := byName.insert `grid grid
  let some history := byName.find? `hist | throwError "missing the selected history"
  let source ← getConstInfo ``SignedCalendarAt.issuedReportSource_atCommonFrame
  let mut claim := mkConst source.name (source.levelParams.map Level.param)
  let mut ty := source.type
  while ty.isForall do
    let .forallE name expected body kind := ty | unreachable!
    let arg ← if kind.isInstImplicit then synthInstance expected
      else if name == `h then pure history
      else match byName.find? name with
        | some recorded => pure recorded
        | none => throwError "missing calendar source parameter {name}"
    claim := mkApp claim arg
    ty := body.instantiate1 arg
  let some (_, published, _) := (← whnf (← inferType claim)).eq? | throwError "expected the equality at the common frame"
  return published

/-- Compare the allocation accepted by the literal native routing program with the
one indexing the source of the original W reports on the same calendar. -/
private def originalLookupSourceOwners : MetaM (Expr × Expr) := do
  let lookup ← getConstInfo ``SignedCalendarAt.frozenLookupAt
  let read ← getConstInfo ``SignedCalendarAt.frozenLookupOwnerReadback
  forallTelescopeReducing lookup.type fun inputs _ => do
    let observation := mkAppN (mkConst read.name (read.levelParams.map Level.param)) inputs
    let actualRoute := (← whnf (← inferType observation)).bindingDomain!
    let some routed ← whnfUntil actualRoute ``Cube.Physical.NativeAssignments.Routed
      | throwError "expected the selected native routing allocation"
    let published ← publishedLookupSource inputs
    let some source ← whnfUntil (← inferType published) ``RoutingISA.Evaluator.SignedPrep.SourceReports
      | throwError "expected the original published report source"
    let physical := routed.getAppArgs.back!
    let mathematical := source.getAppArgs.back!
    return (← mkForallFVars inputs (← mkEq physical mathematical),
      ← mkLambdaFVars inputs (← mkEqRefl physical))

/-- The equality at the original cal, pin, history, and broadcast, including every
selector and group accepted in the native word universe. -/
elab "calendarLookupSourceOwnersType%" : term => do return (← originalLookupSourceOwners).1

/-- Equality of the numerical owner functions used by native routing and the W source. -/
abbrev SignedCalendarAt.LookupSourceOwnerEquality : Prop := calendarLookupSourceOwnersType%

/-- The attained calendar writer allocates every selector and group to the team used
by its original published source. -/
theorem SignedCalendarAt.frozenLookupSourceOwners : SignedCalendarAt.LookupSourceOwnerEquality := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← originalLookupSourceOwners).2
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
