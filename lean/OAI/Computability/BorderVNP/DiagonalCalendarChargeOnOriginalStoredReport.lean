import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportPayment
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalReportScan
import OAI.Computability.BorderVNP.DiagonalCalendarStoredReportFactsAtOriginalInputs
import OAI.Computability.BorderVNP.DiagonalStoredOriginalSourceOperands

/-! # Paying the registered local request with its stored original report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta RoutingISA.FragmentRows

set_option cleanup.letToHave false
set_option maxHeartbeats 21000000
set_option maxRecDepth 28000

private def payAtOriginalStoredReport : MetaM Expr :=
  withCheckedRouteOperands ``routeInputsOnOriginalReports fun inputs _ => do
    let stored := mkAppN (mkConst ``storedReportFactsAtOriginalInputs [.param `nativeIndex]) inputs
    let payer := mkAppN (← mkConstWithLevelParams ``chargeAtEarlierReportedSite) inputs
    let scanner := mkAppN (← mkConstWithLevelParams ``scanAtOriginalReportedInputs) inputs
    forallTelescopeReducing (← inferType stored) fun args _ => do
      let field := args[0]!
      let team := args[1]!
      let original := args.back!
      let (schema, enumeration) ← storedOriginalInputs original
      let some edges := schema.find? `E | throwError "missing original report edges"
      let some identifiers := schema.find? `I | throwError "missing original report identifiers"
      let some ports := schema.find? `P | throwError "missing original report ports"
      let facts := mkAppN stored args
      let layoutAndMarks := mkProj ``And 1 facts
      let scan := mkApp2 scanner field team
      let geometryAndControls := mkProj ``And 1 scan
      let charged := mkAppN (mkApp2 payer field team) #[
        edges, identifiers, ports, enumeration, mkProj ``Subtype 0 original,
        mkProj ``And 0 scan, mkProj ``And 0 facts, mkProj ``And 0 layoutAndMarks,
        mkProj ``And 1 layoutAndMarks, mkProj ``And 0 geometryAndControls, mkProj ``And 1 geometryAndControls]
      let some _ ← whnfUntil (← inferType charged) ``WriterPostRequest.Charge |
        throwError "the original report did not reach the registered native request"
      mkLambdaFVars args charged

open Lean.Elab.Term in
local elab "payAtOriginalStoredReport%" : term => payAtOriginalStoredReport

private def retainLocalCharge {P : Prop} (h : P) : PSigma (fun p : Prop => p) := ⟨P,h⟩

private noncomputable def originalStoredCharge.{nativeIndex} : PSigma (fun p : Prop => p) :=
  retainLocalCharge payAtOriginalStoredReport%

/-- At every original issued field and team, the funded report returned at that
site pays the registered native writer's request. Its saved coordinates,
layout and marks accompany the geometry return and the 37 control words
read by the scanner at that field and team. -/
theorem chargeOnOriginalStoredReport.{nativeIndex} : originalStoredCharge.{nativeIndex}.1 :=
  originalStoredCharge.2

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
