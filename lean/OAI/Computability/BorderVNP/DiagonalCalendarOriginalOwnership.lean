import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarReturnedOwner
import OAI.Computability.BorderVNP.DiagonalRoutedBareOwnerHistory

/-! # The observed native owner on the original signed tuple -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Evaluator

private abbrev NamedArguments := Array (Name × Expr)

private def argument (args : NamedArguments) (name : Name) : MetaM Expr := do
  let some (_, value) := args.find? (fun p => p.1 == name)
    | throwError "missing source argument {name}"
  return value

private def atHead (type : Expr) (name : Name) : MetaM Expr := do
  let some result ← whnfUntil type name | throwError "expected the native source type {name}"
  return result

private def argumentsOf (application : Expr) : MetaM NamedArguments := do
  let some name := application.getAppFn.constName? | throwError "expected a native source declaration"
  let mut type := (← getConstInfo name).type
  let mut args := #[]
  for value in application.getAppArgs do
    let .forallE binder _ body _ := type | throwError "too many source arguments for {name}"
    args := args.push (binder, value)
    type := body
  return args

private def applyNamed (name : Name) (args : NamedArguments) : MetaM Expr := do
  let mut term ← mkConstWithLevelParams name
  let mut type := (← getConstInfo name).type
  while let .forallE binder _ body _ := type do
    term := mkApp term (← argument args binder)
    type := body
  return term

/-- The three routed inputs index a pin, a history, and a subtotal. The result
provides the types of a true route and the reports written on that route. -/
private def preparedFamilies (routes : Expr) : MetaM (Expr × Expr × Expr) := do
  forallBoundedTelescope routes (some 3) fun xs result => do
    unless xs.size == 3 do throwError "expected the pin, history, and subtotal of the source"
    let issued ← atHead result ``Equiv
    let fields ← atHead issued.getAppArgs[1]! ``Sigma
    let routes ← mkLambdaFVars #[xs[1]!] fields.getAppArgs[0]!
    let reports ← mkLambdaFVars #[xs[0]!, xs[1]!] fields.getAppArgs[1]!
    let whole := mkAppN (← mkConstWithLevelParams ``PreparedFields)
      #[← inferType xs[0]!, ← inferType xs[1]!, ← inferType xs[2]!, routes, reports]
    return (whole, routes, reports)

/-- Apply the original-return reindexing lemma to the same candidate receipt
and the two proved equalities for its original exterior and its actual scans. -/
private def originalOwnerTerm : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calibrated route family"
  forallTelescope shape.value fun parameters selected => do
    let roster ← atHead selected ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
    let native := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let (whole, routes, reports) ← preparedFamilies roster
    let physical ← argumentsOf roster
    withLocalDeclD `f whole fun f => do
      let pin := mkProj ``Sigma 0 f
      let historyAndEntries := mkProj ``Sigma 1 f
      let history := mkProj ``Sigma 0 historyAndEntries
      let entries := mkProj ``Sigma 1 historyAndEntries
      let route := mkProj ``Sigma 0 entries
      let proposed := mkProj ``Sigma 1 entries
      let subtotal := mkProj ``Prod 0 proposed
      let rows := mkProj ``Prod 1 proposed
      let receipt := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedOwnershipAtOfCandidates)
        (parameters ++ #[pin, history, subtotal, route, rows])
      let observed ← argumentsOf (← atHead (← inferType receipt) ``PreparationFrame.ReturnedOwnershipAt)
      let arena := mkApp (mkConst ``SignedTaskArena.Layout.cube) (← argument observed `sa)
      let same ← applyNamed ``BootedPinStart.routedBareTuple_owner_observation
        (#[ (`gen, mkConst ``SparseExterior.driver), (`ar, arena), (`Route, routes), (`Report, reports),
            (`routed, native), (`f, f) ] ++ physical)
      let equations ← atHead (← inferType same) ``And
      let exterior ← atHead equations.getAppArgs[0]! ``Eq
      let scans ← atHead equations.getAppArgs[1]! ``Eq
      let proof ← applyNamed ``PreparationFrame.ReturnedOwnershipAt.onOriginal
        (#[ (`x, ← argument observed `exterior), (`y, exterior.getAppArgs[1]!),
            (`template, ← argument observed `template₀), (`before, ← argument observed `run),
            (`after, scans.getAppArgs[1]!), (`real, receipt), (`same, same) ] ++ observed)
      mkLambdaFVars (parameters.push f) proof

local elab "calendarOriginalOwnerType%" : term => do inferType (← originalOwnerTerm)

/-- The original full prepared tuple at each admitted route of the calibrated calendar. -/
abbrev SignedCalendarAt.FrozenOriginalOwnerStatement : Prop := calendarOriginalOwnerType%

/-- The returned writer has the original exterior and chronological owner scans
of the genuine all-team native prefix on this prepared field. -/
theorem SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates :
    SignedCalendarAt.FrozenOriginalOwnerStatement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalOwnerTerm)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
