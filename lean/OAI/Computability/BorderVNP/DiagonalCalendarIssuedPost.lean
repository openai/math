import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalPostOperands
import OAI.Computability.BorderVNP.DiagonalIssuedDataAtRoster

/-! # Physical post requests on the original issued calendar fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

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
private def writerOnOriginalRoute : MetaM Expr := do
  let .defnInfo issuing ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected calendar's issuing routes"
  forallTelescope issuing.value fun parameters result => do
    let some roster ← whnfUntil result ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the original native roster"
    let some i ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the source tables"
    let static := parameters.extract 0 i
    let original := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let writer := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPostWriterAt) static
    let rateType ← whnf (← inferType writer)
    unless rateType.isForall && rateType.bindingName! == `rate do
      throwError "expected the physical post rate after the fixed site arguments"
    withLocalDeclD `rate rateType.bindingDomain! fun rate => do
      let pin ← rosterField roster `pin
      let supplied := mkApp2 writer rate pin
      forallBoundedTelescope (← inferType supplied) (some 5) (whnfType:=true) fun domain request => do
        unless domain.size=5 do throwError "expected exterior, prefix, team, header and its physical reading"
        let payload ← mkLambdaFVars (domain.extract 0 3) request
        let transport ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.collectOnRoutes
        let term := mkAppN transport (roster.getAppArgs ++ #[original,payload,supplied])
        -- The public entry point takes the post rate just before the registered candidate family.
        let args := (parameters.extract 0 (parameters.size-1)) ++ #[rate,parameters.back!]
        mkLambdaFVars args term

local elab "issuedWriterFamily%" : term => do inferType (← writerOnOriginalRoute)

/-- The native post requests at the selected exterior, all-team prefix and team
of every issued calendar field. -/
noncomputable abbrev SignedCalendarAt.IssuedPostRequests : Type _ := issuedWriterFamily%

/-- The original field's reconstructed tuple obtains the deployed writer with
its own positive startup and its own physically observed header. -/
noncomputable def SignedCalendarAt.issuedWriterRequest : SignedCalendarAt.IssuedPostRequests := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← writerOnOriginalRoute)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
