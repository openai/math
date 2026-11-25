import OAI.Computability.BorderVNP.DiagonalCalendarFundedRoster
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalRosterAddresses
import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport

/-! # The supported call roster of an issued report

The source and the supported inverse see the same sparse call. The report retains
its emission, chosen patch, indexed rows, native launch and the equality at its
output memory. We use this data to transport the roster to the planner's addresses
on the same history, report tape, subtotal and team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.FragmentRows RoutingISA.Evaluator.ScheduleClock

private abbrev Recorded := List (Name × Expr)

/-- Recover the arguments of the given kernel application by binder name. -/
private def argumentsAt (type : Expr) (head : Name) : MetaM Recorded := do
  let some applied ← whnfUntil type head | throwError "expected {head} in the issued report"
  let mut signature := (← getConstInfo head).type
  let mut fields := []
  for arg in applied.getAppArgs do
    let .forallE name _ rest _ := signature | throwError "unexpected argument to {head}"
    fields := (name,arg) :: fields
    signature := rest
  return fields

private def retained (fields : Recorded) (names : Array Name) : MetaM (Array Expr) :=
  names.mapM fun name => do
    let some x := fields.lookup name | throwError "missing issued operand {name}"
    return x

/-- Read the exact bank, report memory, team and frame from a supported
roster. Its five existential witnesses are the placed site type, placements,
geometry, extra rows and sparse input. These six parameters precede them. -/
private def receiptParameters : Nat → Expr → MetaM (Array Expr)
  | 0, goal => do
    let roster ← argumentsAt goal ``ProducedRoster
    let some layout := roster.lookup `l | throwError "missing supported control rows"
    let controls ← argumentsAt layout ``RoutingISA.SignedTaskArena.Layout.controlRows
    return (← retained roster #[`w,`pub,`m]) ++ (← retained controls #[`team,`frame]) ++
      (← retained roster #[`raw])
  | n+1, goal => do
    let some found ← whnfUntil goal ``Exists | throwError "missing supported roster witness"
    lambdaBoundedTelescope found.getAppArgs[1]! 1 fun _ body => receiptParameters n body

/-- Apply the supported observer to the actual saved launch. Its input type
records the emission, patch, report row and all their original coordinates. -/
private def rosterOfReport (observer transport issued : Expr) : MetaM Expr := do
  let fields := getStructureFields (← getEnv) ``EmittedReport
  let some launchIx := fields.findIdx? (· == `launch) | throwError "missing issued sparse launch"
  let some outputIx := fields.findIdx? (· == `output_eq) | throwError "missing output memory equality"
  let launch := mkProj ``EmittedReport launchIx issued
  let native ← argumentsAt (← inferType launch) ``SparseEmission.NativeInputAt
  let operands ← retained native #[`a,`f,`orig,`fit,`cells,`e,`team,`offsets,`ctl,`live,`ports,
    `data,`Site,`patch,`row,`description]
  let observed := mkAppN observer (operands ++ #[launch,mkProj ``EmittedReport outputIx issued])
  let parameters ← receiptParameters 5 (← inferType observed)
  return mkAppN transport (parameters.push observed)

/-- Quantify over the directory and labels of the emitted report on this very
prefix. The observer fixes its arena, boots, team, prefix and physical addresses. -/
private def onIssuedReport (observer transport model : Expr) : MetaM Expr := do
  let launch ← argumentsAt model ``SparseEmission.NativeInputAt
  let boot ← retained launch #[`teams,`n,`w,`a,`U,`agent,`p]
  let pointers ← retained launch #[`offsets,`ctl,`live,`ports]
  let report := mkAppN (← mkConstWithLevelParams ``EmittedReport) boot
  forallBoundedTelescope (← inferType report) (some 1) fun directory _ => do
    let addressed := mkAppN report (directory ++ pointers)
    forallTelescope (← inferType addressed) fun labels _ => do
      withLocalDeclD `issued (mkAppN addressed labels) fun saved => do
        mkLambdaFVars (directory ++ labels ++ #[saved]) (← rosterOfReport observer transport saved)

private def originalGeometry (transport : Expr) : MetaM (Expr × Expr × Expr) := do
  forallBoundedTelescope (← inferType transport) (some 6) fun _ implication => do
    let .forallE _ source _ _ ← whnf implication | throwError "expected the planner address implication"
    let fields ← argumentsAt source ``RosterAtReportAddresses
    let values ← retained fields #[`a,`ports,`addr]
    return (values[0]!,values[1]!,values[2]!)

/-- Specialize the supported observer to the original emitter geometry. The
temporary emission and launch arguments expose the original return type.
The resulting proof takes its witnesses from the issued report itself. -/
private def issuedRosterProof : MetaM Expr := do
  let route ← mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs
  forallTelescope (← inferType route) fun operands _ => do
    let calibrated := operands.extract 0 (operands.size-3)
    let some values ← calibrated.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "missing original calendar values"
    let observer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRosterOnRoute) calibrated
    let transport := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedRosterAtPlanner)
      (calibrated.extract 0 values)
    let (arena,ports,addr) ← originalGeometry transport
    let tail := mkProj ``Prod 1 addr
    let pointers := #[mkProj ``Prod 0 addr,mkProj ``Prod 0 tail,mkProj ``Prod 1 tail,ports]
    forallBoundedTelescope (← inferType observer) (some 3) fun selected _ => do
      let supported := mkAppN observer selected
      let atArena := mkApp supported arena
      let team ← mkAppM ``Fin.val #[selected[2]!]
      forallBoundedTelescope (← inferType atArena) (some 5) fun emission _ => do
        let returned := mkAppN atArena ((emission.push team) ++ pointers)
        forallTelescope (← inferType returned) fun fields _ => do
          let model ← inferType fields[fields.size-2]!
          mkLambdaFVars (calibrated ++ selected) (← onIssuedReport supported transport model)

local elab "issuedReportRosterStatement%" : term => do inferType (← issuedRosterProof)

/-- The supported roster on the planner's literal return for each emitted
report on an original calendar field. -/
abbrev SignedCalendarAt.IssuedReportRoster : Prop := issuedReportRosterStatement%

/-- A physical report on the selected pin, history, report tape and team
supplies the planner's placed cells, geometry, extra rows and sparse argument input. -/
theorem SignedCalendarAt.rosterOnIssuedReport : SignedCalendarAt.IssuedReportRoster := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← issuedRosterProof)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
