import OAI.Computability.BorderVNP.DiagonalCalendarOriginalChart

/-! # The original funded report chart at the issued argument address -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta RoutingISA.SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open Packing.RoutingOutputs

private theorem controlOfNetwork (installed planner : Layout) (cells cables origin entries ports : ℕ)
    (same : installed.withNetwork cells cables=planner) :
    controlsBase origin planner.cube.cables planner.cube.cells entries ports =
      controlsBase origin cables cells entries ports := by
  subst planner
  rfl

private theorem changeChartControl (pre : BeforeTasks) (post : AfterTasks)
    (frame control issued h H body zeroAddr : ℕ) (original : ReportLayout)
    (same : control=issued) (chart : original=reportLayout pre post frame control h H body zeroAddr) :
    original=reportLayout pre post frame issued h H body zeroAddr := by
  subst issued
  exact chart

private def applied (x : Expr) (head : Name) : MetaM Expr := do
  let some app ← whnfUntil x head | throwError "expected {head} in the funded chart"
  return app

/-- The existing boot theorem records the original chart and native control word.
Read its actual operands and transport only the cable and cell counts of that word. -/
private def chartAtIssuedControl : MetaM Expr := do
  let boot ← mkConstWithLevelParams ``SignedCalendarAt.frozenOriginalPlannerLayout_on_boot
  forallTelescopeReducing (← inferType boot) fun xs result => do
    let some cut ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `chargeFit)
      | throwError "expected the calibrated reader before the chosen team"
    let shape := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPlannerTask_eq) (xs.extract 0 (cut+1))
    let geometry := (← applied (← inferType shape) ``Eq).getAppArgs
    let network := (← applied geometry[1]! ``Layout.withNetwork).getAppArgs
    let sides := (← applied result ``Eq).getAppArgs
    let chart := (← applied sides[2]! ``reportLayout).getAppArgs
    let pointer := (← applied chart[3]! ``controlsBase).getAppArgs
    let move := mkAppN (← mkConstWithLevelParams ``controlOfNetwork)
      #[network[0]!,geometry[2]!,network[1]!,network[2]!,pointer[0]!,pointer[3]!,pointer[4]!,shape]
    let target := mkAppN (mkConst ``controlsBase)
      #[pointer[0]!,network[2]!,network[1]!,pointer[3]!,pointer[4]!]
    let proof := mkAppN (← mkConstWithLevelParams ``changeChartControl)
      (chart.extract 0 4 ++ #[target] ++ chart.extract 4 chart.size ++ #[sides[1]!,move,mkAppN boot xs])
    mkLambdaFVars xs proof

set_option maxRecDepth 12000
set_option maxHeartbeats 2300000

local elab "fundedSourceChart%" : term => do inferType (← chartAtIssuedControl)

/-- The emitted report chart at all original calibration parameters and startup states. -/
abbrev SignedCalendarAt.FundedChartAtIssuedControl : Prop := fundedSourceChart%

/-- At each actual team boot, the recorded report layout uses the issued control
pointer for the published cable and cell counts of that same planner. -/
theorem SignedCalendarAt.frozenFundedLayoutAtIssuedControl : SignedCalendarAt.FundedChartAtIssuedControl := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← chartAtIssuedControl)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
