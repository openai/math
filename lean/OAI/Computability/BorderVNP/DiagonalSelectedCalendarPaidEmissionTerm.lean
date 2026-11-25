import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalCalendarMarkedReportEmission
import OAI.Computability.BorderVNP.DiagonalSelectedCalendarObservation
import OAI.Computability.BorderVNP.DiagonalReturnedEntryPlacement

/-! # The paid argument emitter on the selected report opening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term FiniteEvaluator RoutingISA.Evaluator

private def argumentNames (declaration : Name) : MetaM (Array Name) := do
  let c ← getConstInfo declaration
  forallTelescope c.type fun xs _ => xs.mapM fun x => x.fvarId!.getUserName

open private storedLookupTerm from OAI.Computability.BorderVNP.DiagonalSelectedCalendarObservation

private def emissionAtRecordedCalendar (lookup : Expr) : MetaM Expr := do
  let sel ← storedLookupTerm lookup
  unless sel.isAppOf ``SignedCalendarAt.frozenLookupAt do throwError "expected the recorded calendar lookup"
  let xs := sel.getAppArgs
  let labels ← argumentNames ``SignedCalendarAt.frozenLookupAt
  let some opAt := labels.idxOf? `oper | throwError "missing the native operating calendar"
  let some vAt := labels.idxOf? `values | throwError "missing the original value table"
  let some hAt := labels.idxOf? `hist | throwError "missing its history"
  let oper := xs[opAt]!
  let grid ← mkProjection oper `grid
  let funding ← mkProjection oper `funding
  let statics := xs.extract 0 opAt ++ #[grid] ++ xs.extract (opAt+1) vAt
  return mkAppN (Lean.mkConst ``SignedCalendarAt.frozenMarkedReportEmission sel.getAppFn.constLevels!)
    (statics ++ #[funding,xs[vAt]!,xs[hAt]!])

private def routeAtRecordedCalendar (lookup row admitted : Expr) : MetaM Expr := do
  let emitter ← emissionAtRecordedCalendar lookup
  let .forallE _ target _ _ ← whnf (← inferType emitter)
    | throwError "expected the native emitter's route"
  let some route ← whnfUntil target ``Subtype | throwError "expected an admitted original route"
  return mkAppN (Lean.mkConst ``Subtype.mk route.getAppFn.constLevels!)
    (route.getAppArgs ++ #[row,admitted])

/-- Put the observed row in the original emitter's own route type, retaining
the admission proof supplied by the registered source. -/
elab "originalPaidRoute%" lookup:term:max row:term:max admitted:term:max : term => do
  routeAtRecordedCalendar (← elabTerm lookup none) (← elabTerm row none) (← elabTerm admitted none)

private def markedEmissionAtReturn (lookup route team advance report axis input marks ready place : Expr) : MetaM Expr := do
  let emitter ← emissionAtRecordedCalendar lookup
  let some returned ← whnfUntil (← inferType advance) ``Returns
    | throwError "expected the actual control return"
  let #[_,_,pub,mac,regs,ownedMem] := returned.getAppArgs
    | throwError "unexpected control machine parameters"
  let some entry ← whnfUntil (← inferType ready) ``OpenSuffix.Ready
    | throwError "expected the selected entry's ready control suffix"
  let #[stage,_,_,_] := entry.getAppArgs | throwError "unexpected native suffix arguments"
  let some issuance ← whnfUntil (← inferType marks) ``SignedCalendarAt.frozenIssuedMarkers
    | throwError "expected the original geometry RAM marker"
  let ram := issuance.getAppArgs.back!
  return mkAppN emitter #[route,team,pub,mac,regs,ownedMem,stage,advance,report,axis,input,
    ram,marks,ready,place]

/-- Specialize the paid emitter on the selected calendar, actual machine return
and native marker. Its remaining arguments start after the opening placement. -/
elab "paidAtSelectedReturn%" lookup:term:max route:term:max team:term:max advance:term:max
    report:term:max axis:term:max input:term:max marks:term:max ready:term:max place:term:max : term => do
  let arguments ← #[lookup,route,team,advance,report,axis,input,marks,ready,place].mapM fun t => elabTerm t none
  markedEmissionAtReturn arguments[0]! arguments[1]! arguments[2]! arguments[3]! arguments[4]!
    arguments[5]! arguments[6]! arguments[7]! arguments[8]! arguments[9]!

end Diagonal

end BorderVNP
end Computability
end OAI
