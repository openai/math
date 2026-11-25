import OAI.Computability.BorderVNP.DiagonalCalendarPinnedReportCut
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs
import OAI.Computability.BorderVNP.DiagonalBareAssignmentReturns

/-! # Chronological cell reports on the original calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction TeamContraction.ProcessorSlots
open PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

set_option autoImplicit false
set_option maxRecDepth 14000
set_option maxHeartbeats 12000000
set_option Elab.async false

private def namedArgs (head : Name) (args : Array Expr) : MetaM (Std.HashMap Name Expr) := do
  let ci ← getConstInfo head
  forallBoundedTelescope ci.type (some args.size) fun bs _ => do
    unless bs.size == args.size do throwError "{head}: incomplete telescope"
    let mut tab : Std.HashMap Name Expr := {}
    for b in bs, a in args do
      tab := tab.insert (← b.fvarId!.getDecl).userName.eraseMacroScopes a
    return tab

private def lookupArg (m : Std.HashMap Name Expr) (n : Name) : MetaM Expr := do
  let some x := m.get? n | throwError "missing original argument {n}"
  return x

/-- Reuse the actual route family, real supplied frames, and report rows. The proof on a
single header comes directly from the original accepted calendar point-cut theorem. -/
private def originalCalendarReturns : MetaM Expr := do
  let .defnInfo orig ← getConstInfo ``SignedCalendarAt.frozenRoutedInputs
    | throwError "expected the original routed-inputs definition"
  lambdaTelescope orig.value fun xs body => do
    unless xs.size ≥ 3 do throwError "the original route needs its input, history and claim"
    let leading := xs.extract 0 (xs.size-3)
    let fields := xs.extract (xs.size-3) xs.size
    let input := fields[0]!
    let hist := fields[1]!
    let some bound ← whnfUntil body ``SignedCalendarAt.frozenRoutedAt
      | throwError "the original inputs must invoke the native calendar route"
    let single := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPinnedReportCutAt) bound.getAppArgs
    let some admitted ← whnfUntil body ``signedAdmittedRouting
      | throwError "the calendar must invoke the original admitted route"
    let native ← namedArgs ``signedAdmittedRouting admitted.getAppArgs
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs) leading
    let some target ← whnfUntil (← inferType body) ``Equiv
      | throwError "expected the calendar's preparation equivalence"
    let some rowTuple ← whnfUntil target.appArg! ``Sigma
      | throwError "expected a routed selection paired with its team reports"
    let sigmaArgs := rowTuple.getAppArgs
    unless sigmaArgs.size == 2 do throwError "malformed report tuple"
    let routes ← mkLambdaFVars #[hist] sigmaArgs[0]!
    let reports ← mkLambdaFVars #[input,hist] sigmaArgs[1]!
    withLocalDeclD `z rowTuple fun z => do
      let selected := mkProj ``Sigma 0 z
      let supplied := mkProj ``Sigma 1 z
      let selectedCut := mkAppN single #[selected,supplied]
      let .forallE _ team _ _ ← whnf (← inferType selectedCut)
        | throwError "a source report must be available at every native team"
      withLocalDeclD `u team fun u => do
        let some point ← whnfUntil (← inferType (mkApp selectedCut u)) ``pinnedReportCutAt
          | throwError "the native calendar supplied a different source observation"
        let p := point.getAppArgs
        unless p.size ≥ 3 do throwError "missing source layout, cell list or rows"
        let rowKey := mkAppN (← mkConstWithLevelParams ``ReportInputKey.ofRows) (p.extract (p.size-3) p.size)
        let key ← mkLambdaFVars #[input,hist,z,u] rowKey
        let cuts ← mkLambdaFVars fields single
        let pointArgs ← namedArgs ``pinnedReportCutAt p
        let constructor := ``BootedPinStart.bareReturnPackageOfPointCuts
        let ci ← getConstInfo constructor
        forallTelescope ci.type fun bs _ => do
          let args ← bs.mapM fun b => do
            let n := (← b.fvarId!.getDecl).userName.eraseMacroScopes
            if n == `routed then return routed
            if n == `key then return key
            if n == `cuts then return cuts
            if n == `Hist then return ← inferType hist
            if n == `Route then return routes
            if n == `Report then return reports
            if n == `pub || n == `reg then return ← lookupArg native n
            if n == `B then return ← lookupArg native `B₀
            if n == `code then return ← lookupArg native `enc
            if n == `headerWidth then return ← lookupArg pointArgs `width
            if n == `pin then return ← lookupArg pointArgs `live
            lookupArg pointArgs n
          let result := mkAppN (← mkConstWithLevelParams constructor) args
          mkLambdaFVars leading result

local elab "originalCalendarReturnsType%" : term => do
  inferType (← originalCalendarReturns)

/-- The chronological cuts indexed by the original calendar's fields and teams. -/
abbrev SignedCalendarAt.OriginalBareReturnType := originalCalendarReturnsType%

/-- The pre-call decoder's true chronological report cuts on every original field and team. -/
noncomputable def SignedCalendarAt.frozenBareReportAssignments : SignedCalendarAt.OriginalBareReturnType := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← originalCalendarReturns)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
