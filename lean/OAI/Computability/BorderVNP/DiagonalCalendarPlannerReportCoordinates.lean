import OAI.Computability.BorderVNP.DiagonalCalendarPlannerMeanOwner
import OAI.Computability.BorderVNP.DiagonalCalendarWriterPacketLabel

/-! # The planner's registered owner acts on the actual funded packet's coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Cube.Physical Packing.RoutingOutputs

private def fieldOf (e : Expr) (head field : Name) : MetaM Expr := do
  let some term ← whnfUntil e head | throwError "expected {head} when reading {field}"
  let mut binders := (← getConstInfo head).type
  for x in term.getAppArgs do
    if binders.bindingName! == field then return x
    binders := binders.bindingBody!
  throwError "missing coordinate {field} in {head}"

private def right (p : Expr) : MetaM Expr := do
  let some e ← whnfUntil (← inferType p) ``Eq | throwError "expected equality at the packet coordinates"
  return e.getAppArgs[2]!

private def fundedCoordinates (statement : Bool) : MetaM Expr := do
  let native ← mkConstWithLevelParams ``SignedCalendarAt.frozenSites_meanOwner
  let planner ← mkConstWithLevelParams ``SignedCalendarAt.frozenSites_plannerMeanOwner
  let packet ← mkConstWithLevelParams ``SignedCalendarAt.frozenWriter_packetLabel
  forallTelescope (← inferType native) fun xs _ => do
    let nativeOwner ← right (mkAppN native xs)
    let plannedOwner ← right (mkAppN planner xs)
    let receiver ← fieldOf nativeOwner ``greedyOwner `recv
    let bounds ← fieldOf receiver ``NativeDemands.receiver `bounds
    let atPacket := mkAppN packet (xs.push bounds)
    let some labels ← whnfUntil (← inferType atPacket) ``Eq | throwError "expected the actual funded packet label"
    let label := labels.getAppArgs[1]!
    let plannedLabel ← fieldOf plannedOwner ``greedyOwner `label
    let plannedReceiver ← fieldOf plannedOwner ``greedyOwner `recv
    let widths ← fieldOf nativeOwner ``greedyOwner `dataWidth
    let plannedWidths ← fieldOf plannedOwner ``greedyOwner `dataWidth
    let p ← mkEq label plannedLabel
    let q ← mkEq receiver plannedReceiver
    let r ← mkEq widths plannedWidths
    if statement then mkForallFVars xs (mkAnd p (mkAnd q r))
    else
      let raw := mkApp4 (mkConst ``And.intro) p (mkAnd q r) atPacket
        (mkApp4 (mkConst ``And.intro) q r (← mkEqRefl receiver) (← mkEqRefl widths))
      mkLambdaFVars xs raw

set_option maxRecDepth 15000
set_option maxHeartbeats 5200000
local elab "fundedCoordinateStatement%" : term => fundedCoordinates true

/-- The packet label and the original receiver and row widths agree with the
coordinate functions of the planner's registered greedy owner. -/
abbrev SignedCalendarAt.PlannerReportCoordinates : Prop := fundedCoordinateStatement%

/-- The calibration reindexes the genuine ordered packet with the same
labels, receiving cells and incoming widths used by the native argument window. -/
theorem SignedCalendarAt.frozenPlannerReportCoordinates : SignedCalendarAt.PlannerReportCoordinates := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← fundedCoordinates false)
    Lean.Elab.Tactic.replaceMainGoal []


end Diagonal

end BorderVNP
end Computability
end OAI
