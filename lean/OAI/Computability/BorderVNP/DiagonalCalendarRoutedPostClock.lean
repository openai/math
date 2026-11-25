import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPost
import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarPostClockAtSource
import OAI.Computability.BorderVNP.DiagonalIssuedHeaderAssertions

/-! # Clock readback on the issued calendar fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

set_option maxRecDepth 9000
set_option maxHeartbeats 1400000

private def rosterField (application : Expr) (field : Name) : MetaM Expr := do
  let some family := application.getAppFn.constName? | throwError "expected the route's named type"
  let mut type := (← getConstInfo family).type
  for value in application.getAppArgs do
    if type.bindingName! == field then return value
    type := type.bindingBody!.instantiate1 value
  throwError "missing route field {field}"

/-- Apply the physical native writer to its own roster in the installed calendar.
The three arguments of its payload are the real positive exterior, joint prefix,
and team number. The writer takes their actual observed header. -/
private def clockAtOriginalRoute : MetaM Expr := do
  let .defnInfo issuing ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected calendar's issuing routes"
  forallTelescope issuing.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the original native roster"
    let some i ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the source tables"
    let static := parameters.extract 0 i
    let original := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let writer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPostWriterClockAt) static
    let rateType ← whnf (← inferType writer)
    unless rateType.isForall && rateType.bindingName! == `rate do
      throwError "expected the physical post rate after the fixed site arguments"
    withLocalDeclD `rate rateType.bindingDomain! fun rate => do
      let pin ← rosterField roster `pin
      let supplied := mkApp2 writer rate pin
      let selected := parameters.pop ++ #[rate,parameters.back!]
      let issued := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedWriterRequest) selected
      let some originalWriter ← withTransparency .all <|
          whnfUntil issued ``BootedPinStart.PreparedHistoryDecoder.collectOnRoutes
        | throwError "expected the writer supplied on the exact original field"
      let physicalSource := originalWriter.getAppArgs.back!
      forallBoundedTelescope (← inferType supplied) (some 5) (whnfType:=true) fun domain request => do
        unless domain.size=5 do throwError "expected exterior, prefix, team, header and its physical reading"
        let .forallE _ received measured _ ← whnf request
          | throwError "expected the deployed charge to imply the native scalar bound"
        unless !measured.hasLooseBVar 0 do throwError "the native clock must be independent of the charge proof"
        let some charge ← whnfUntil received ``RoutingISA.FragmentRows.WriterPostRequest.Charge
          | throwError "expected the physical writer charge"
        let actual := mkAppN physicalSource domain
        let source ← mkLambdaFVars domain
          (mkAppN charge.getAppFn (charge.getAppArgs.pop.push actual))
        let target ← mkLambdaFVars domain (measured.instantiate1 (mkConst ``True.intro))
        let transport ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.headerAssertionsMap
        let term := mkAppN transport (roster.getAppArgs ++ #[original,source,target,supplied])
        -- The public entry point takes the post rate just before the registered candidate family.
        mkLambdaFVars selected term

local elab "originalPostClock%" : term => do inferType (← clockAtOriginalRoute)

/-- The implication between the calibrated writer charge and the literal native
clock at each original issued exterior and team. -/
abbrev SignedCalendarAt.RoutedPostClock : Prop := originalPostClock%

/-- Reading the charged request at every original supported field gives the
explicit native post clock on the same calibrated tuple. -/
theorem SignedCalendarAt.issuedClockOfPostRequests : SignedCalendarAt.RoutedPostClock := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← clockAtOriginalRoute)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
