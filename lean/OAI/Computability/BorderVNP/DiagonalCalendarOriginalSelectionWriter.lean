import OAI.Computability.BorderVNP.DiagonalCalendarReturnedWriterAtExterior
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedNativeGuess
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedObservedAt
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerPostOperands
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedSourceExterior
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs
import OAI.Computability.BorderVNP.DiagonalCalendarOwnerAdmission
import OAI.Computability.BorderVNP.DiagonalReturnedSourceExterior

/-! # The physical writer on an original field of the enrolled calendar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Evaluator

set_option cleanup.letToHave false
set_option maxRecDepth 18000
set_option maxHeartbeats 6200000

private def sourceInputs (type : Expr) (head : Name) : MetaM (NameMap Expr) := do
  let some app ← whnfUntil type head | throwError "expected {head} at the original field"
  let mut signature := (← getConstInfo head).type
  let mut result : NameMap Expr := {}
  for v in app.getAppArgs do
    result := result.insert signature.bindingName! v
    signature := signature.bindingBody!
  return result

private def sourceInput (fields : NameMap Expr) (name : Name) : MetaM Expr := do
  let some v := fields.find? name | throwError "missing original writer input {name}"
  return v

private def nextInput (term : Expr) : MetaM Expr := do
  let .forallE _ ty _ _ ← whnf (← inferType term) | throwError "expected an enrolled field or returned site"
  return ty

/-- Restore exactly the field, source, frame and native prefix of the recorded
writer. Apart from the per-field physical site and the team, all inputs below
are taken from the actual original field, ownership and reader at that field. -/
private def writerOnOriginalSites (restored original owners requests guesses observed agreement
    allowed valid cut : Expr) : MetaM Expr := do
  withLocalDeclD `f (← nextInput original) fun f => do
    let exterior := mkApp original f
    let i := mkProj ``Sigma 0 f
    let records := mkProj ``Sigma 1 f
    let history := mkProj ``Sigma 0 records
    let clauses := mkProj ``Sigma 1 records
    let claim := mkProj ``Prod 0 (mkProj ``Sigma 1 clauses)
    let originData ← sourceInputs (← inferType (mkApp owners f)) ``PreparationFrame.ReturnedOwnershipAt
    let task ← sourceInput originData `sa
    let arena := mkApp (mkConst ``SignedTaskArena.Layout.cube) task
    let q ← sourceInput originData `v
    let raw := mkAppN (← mkConstWithLevelParams ``SignedPrep.routeBroadcast)
      #[← sourceInput originData `R, arena,← sourceInput originData `owners,q]
    let ok := mkApp2 allowed history q
    let frames := mkProj ``CheckedRouteInputs 0 (mkAppN valid #[i,history,claim])
    let align := mkApp (mkProj ``AdmittedPinnedFrames 1 frames) (mkProj ``Subtype 0 raw)
    let frame ← sourceInput originData `F
    let atFrame := mkAppN restored #[i,history,claim,raw,ok,← sourceInput originData `L,align,frame]
    withLocalDeclD `selected (← nextInput atFrame) fun selected => do
      let reached := mkApp2 atFrame selected (← sourceInput originData `origin)
      withLocalDeclD `u (← nextInput reached) fun u => do
        let seen := mkApp2 observed f cut
        let some eqn ← whnfUntil (← inferType seen) ``Eq | throwError "expected original observed header"
        let some bits ← whnfUntil eqn.getAppArgs[2]! ``JointHeader.PositiveFields.bits | throwError "expected positive fields"
        let proof := mkAppN reached #[u,mkProj ``Sigma 0 exterior,mkApp agreement f,mkProj ``Sigma 1 exterior,
          mkApp guesses f,bits.getAppArgs.back!,← mkEqSymm seen]
        let some inhabited ← whnfUntil (← inferType proof) ``Nonempty | throwError "expected the physical writer"
        let some did ← whnfUntil inhabited.getAppArgs[0]! ``FragmentRows.WriterPostRequest.PublishedWriter
          | throwError "expected the retained frame's own writer"
        let native := mkProj ``Subtype 0 (mkApp2 requests f u)
        let issued := mkAppN did.getAppFn (did.getAppArgs.pop.push native)
        let sameReport := mkApp2 (mkConst ``id [.zero]) (mkApp inhabited.getAppFn issued) proof
        mkLambdaFVars #[f,selected,u] sameReport

/-- Read the native calendar and its operative frame from the two real
public interfaces. Before the field and team the parameters differ only by
the operative execution carrying the grid; the actual pin and claims stay fixed. -/
private def writerForAdmittedInput : MetaM Expr := do
  let .defnInfo route ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the enrolled issuing route"
  let returned ← mkConstWithLevelParams ``SignedCalendarAt.publishedWriterAtRestoredExterior
  forallBoundedTelescope (← inferType returned) (some (route.value.getForallArity-2)) fun xs next => do
    unless next.bindingName! == `i do throwError "expected the original candidate's first native pin"
    let some pos ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `oper)
      | throwError "missing operative native execution"
    let some vals ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "missing source table"
    let exec := xs[pos]!
    let grid ← mkProjection exec `grid
    let rate ← mkProjection exec `post
    let native := xs.set! pos grid
    let afterPin ← instantiateForall route.value native
    forallBoundedTelescope afterPin (some 2) fun data roster => do
      let parameters := native ++ data
      let service (name : Name) := do return mkAppN (← mkConstWithLevelParams name) parameters
      let physical ← sourceInputs roster ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      let requests := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedPlannerPostOperands)
        (parameters.pop++#[rate,parameters.back!])
      let admit := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRouteAllowedForOwner)
        (native.extract 0 (vals+1))
      let proof ← writerOnOriginalSites (mkAppN returned xs) (← service ``SignedCalendarAt.issuedBareTupleAtOfCandidates)
        (← service ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates) requests
        (← service ``SignedCalendarAt.issuedOriginalGuessOfCandidates) (← service ``SignedCalendarAt.issuedObservedAtOfCandidates)
        (← service ``SignedCalendarAt.issuedSourceExteriorOfCandidates) admit data[1]! (← sourceInput physical `fixed)
      mkLambdaFVars (xs++data) proof

local elab "originalWriterSelection%" : term => do inferType (← writerForAdmittedInput)

/-- The selected physical source of every field in the calendar's original issuing family. -/
abbrev SignedCalendarAt.OriginalWriterSelection : Prop := originalWriterSelection%

/-- At each restored field of the original accepted declarations, reading the
physical publication of the same enrolled frame gives that field's actual
native writer and final request on every team. -/
theorem SignedCalendarAt.publishedWriterOnOriginalSelectionOfCandidates : SignedCalendarAt.OriginalWriterSelection := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← writerForAdmittedInput)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
