import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSelectionArgument
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSelectionWriter
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportOperation
import OAI.Computability.BorderVNP.DiagonalEmittedNativeWindow

/-! # Charging a funded emission on its original selected frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA RoutingISA.FragmentRows

set_option cleanup.letToHave false
set_option maxRecDepth 22000
set_option maxHeartbeats 10500000

private def routeCheckBinder : Expr → Option Nat
  | .forallE name _ body _ =>
    if name == `valid then some 1 else (routeCheckBinder body).map Nat.succ
  | .mdata _ body => routeCheckBinder body
  | _ => none

/-- Count the calendar parameters through the family's own returned route
checker. The field and the selected site are its subsequent inputs. -/
def SignedCalendarAt.originalSelectionParameters (statement : Expr) : MetaM Nat := do
  let some size := routeCheckBinder (← whnf statement)
    | throwError "expected the original signed route checker"
  return size

private def nextReportInput (operation : Expr) : MetaM Expr := do
  let .forallE _ ty _ _ ← whnf (← inferType operation)
    | throwError "expected another original report input"
  return ty

/-- The home table in the physical report determines the number of bundles. -/
private def reportBundles (argument : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType argument) (some 2) fun args _ => do
    let .forallE _ key _ _ ← whnf (← inferType args[1]!)
      | throwError "expected the home table of the issued bundles"
    let some count ← whnfUntil key ``Fin | throwError "expected a bounded bundle index"
    return count.getAppArgs.back!

private def nativeWindow (finding : Expr) : MetaM Expr := do
  let assignments ← mkAppM ``Exists.choose_spec #[finding]
  let observed ← mkAppM ``Exists.choose_spec #[assignments]
  mkAppM ``Exists.choose #[mkProj ``And 1 observed]

/-- Use the emitted packet's own open header, prepared layout, sparse emitter
and returned memory in the measured argument. The result is the source
window on the same packet for which the writer issues the final charge. -/
private def payReturnedReport (argument writer directory request pay : Expr) : MetaM Expr := do
  let bundles ← reportBundles argument
  forallBoundedTelescope (← inferType pay) (some 4) fun schema _ => do
    let receive := mkAppN pay (schema.push bundles)
    withLocalDeclD `d (← nextReportInput receive) fun d => do
      let issued ← mkProjection d `issued
      let report := mkAppN argument #[← mkProjection issued `headerBits, ← mkProjection d `home,
        ← mkProjection issued `header, ← mkProjection issued `ready]
      withLocalDeclD `reported (← nextReportInput report) fun reported => do
        let finding := mkAppN report #[reported, ← mkProjection d `fit, ← mkProjection d `cells,
          ← mkProjection d `emission, ← mkProjection d `output_eq]
        let atReport := mkApp receive d
        withLocalDeclD `coordinates (← nextReportInput atReport) fun coordinates => do
          let rate := mkProj ``And 1 (mkProj ``And 1 (mkProj ``Subtype 1 request))
          let window ← mkAppM ``EmittedReport.windowFromNative
            #[d, coordinates, rate, ← nativeWindow finding]
          let charge := mkApp2 atReport coordinates window
          withLocalDeclD `layout (← nextReportInput charge) fun layout => do
            let owner := mkApp2 charge layout directory
            forallBoundedTelescope (← inferType owner) (some 3) fun rows _ => do
              let proof := mkApp (mkAppN owner rows) (← mkAppM ``Classical.choice #[writer])
              mkLambdaFVars (schema ++ #[d,reported,coordinates,layout] ++ rows) proof

/-- Supply the original executable grid, selected frame and actual post rate
at all the parameters of the returned argument theorem. -/
private def chargeOnReturnedSelection : MetaM Expr := do
  let argument ← mkConstWithLevelParams ``SignedCalendarAt.argumentOnOriginalSelection
  let initial ← inferType argument
  let count ← SignedCalendarAt.originalSelectionParameters initial
  forallBoundedTelescope initial (some count) fun inputs _ => do
    let some channel ← inputs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `oper)
      | throwError "missing the operative native execution"
    let oper := inputs[channel]!
    let valid := inputs.back!
    let native ← forallBoundedTelescope (← inferType valid) (some 3) fun _ result => do
      let some checked ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks
        | throwError "expected the source pin, history and subtotal checks"
      let args := checked.getAppArgs
      return (args.extract 0 (args.size-3)).push valid
    let mut route := (← getConstInfo ``SignedCalendarAt.FrozenRouteChecks).type
    let mut operative := native
    for i in [:native.size-1] do
      if route.bindingName! == `grid then operative := operative.set! i oper
      route := route.bindingBody!
    let funded := native.pop ++ #[← mkProjection oper `post,valid]
    let payments := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.chargeReportOnOriginal) funded
    let requests := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedPlannerPostOperands) funded
    let writers := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.publishedWriterOnOriginalSelectionOfCandidates) operative
    let physical := mkAppN argument inputs
    withLocalDeclD `f (← nextReportInput writers) fun f => do
      withLocalDeclD `selected (← nextReportInput (mkApp writers f)) fun selected => do
        let source := mkApp2 writers f selected
        let directory ← mkProjection (← mkProjection selected `projection) `directory
        withLocalDeclD `u (← nextReportInput source) fun u => do
          let proof ← payReturnedReport (mkAppN physical #[f,selected,u]) (mkApp source u) directory
            (mkApp2 requests f u) (mkApp2 payments f u)
          mkLambdaFVars (inputs ++ #[f,selected,u]) proof

local elab "originalSelectionChargeType%" : term => do inferType (← chargeOnReturnedSelection)

/-- The charged native result on the report of each selected original field. -/
abbrev SignedCalendarAt.OriginalSelectionCharge : Prop := originalSelectionChargeType%

/-- The selected candidate's actual argument window and published writer
charge its original emitted report at the rate of the operative calendar. -/
theorem SignedCalendarAt.chargeReportAtOriginalSelection : SignedCalendarAt.OriginalSelectionCharge := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← chargeOnReturnedSelection)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
