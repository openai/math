import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldWriter
import OAI.Computability.BorderVNP.DiagonalVisitedRetainedReportWords

/-! # The signed report following an issued field's original native writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term RoutingISA RoutingISA.Evaluator TeamContraction

set_option cleanup.letToHave false
set_option maxRecDepth 22000
set_option maxHeartbeats 12000000

private def argumentOf (app : Expr) (key : Name) : MetaM Expr := do
  let info ← getConstInfo app.getAppFn.constName!
  let mut type := info.type
  for value in app.getAppArgs do
    let .forallE binder _ body _ := type | throwError "unexpected argument to {info.name}"
    if binder == key then return value
    type := body
  throwError "missing {key} in {info.name}"

/-- Follow the projections reading the memory of the original owned return. -/
private partial def originalVisit (read : Expr) : MetaM Expr := do
  if read.isAppOf ``PinStart.visits then return read
  match read with
  | .app _ arg | .proj _ _ arg | .mdata _ arg => originalVisit arg
  | _ => throwError "expected the native visit whose owned RAM the writer retained"

private def wordsFollowingWriter (kept : Expr) : MetaM Expr := do
  let some state ← whnfUntil (← inferType kept) ``FiniteEvaluator.CubeAllocation.HostRetention
    | throwError "expected the slotted writer's actual retained publication"
  let arena ← argumentOf state `a
  unless arena.isAppOf ``SignedTaskArena.Layout.cube do throwError "expected the selected native task's cube"
  let visit ← originalVisit (← argumentOf state `returned)
  let some initial ← whnfUntil (← argumentOf state `initial) ``RoutingISA.readings
    | throwError "expected readings from the initial physical RAM"
  let some published ← whnfUntil (← argumentOf initial `s) ``Packing.Directory.ISA.publish
    | throwError "expected the directory published in the writer's initial RAM"
  let frame ← argumentOf published `frame
  let args := #[← argumentOf visit `R, ← argumentOf visit `n, ← argumentOf visit `w, arena.appArg!,
    ← argumentOf visit `U, ← argumentOf visit `u, ← argumentOf visit `localRun,
    ← argumentOf published `m, frame, ← argumentOf published `base, ← argumentOf published `rows,
    ← argumentOf state `written, ← mkEqRefl frame, kept]
  return mkAppN (← mkConstWithLevelParams ``PinStart.retainedReportWords) args

private def reportOnSelectedWriter : MetaM Expr := do
  let writer ← mkConstWithLevelParams ``SignedCalendarAt.writerOnOriginalSelection
  forallTelescopeReducing (← inferType writer) fun inputs _ => do
    let stored := mkAppN writer inputs
    let emitted := mkProj ``And 0 (mkProj ``And 0 stored)
    let slotted := mkProj ``And 1 (mkProj ``And 1 (mkProj ``And 1 emitted))
    let words ← wordsFollowingWriter (mkProj ``And 1 stored)
    let result := mkAppN (mkConst ``And.intro) #[← inferType slotted, ← inferType words, slotted, words]
    mkLambdaFVars inputs result

local elab "originalFieldReportWords%" : term => reportOnSelectedWriter

private noncomputable def originalFieldReports : PSigma fun claim : Prop => claim :=
  ⟨_,originalFieldReportWords%⟩

/-- Each issued field's selected native writer supplies a slotted directory. Its
signed report reads the publication retained through that team's original owned return. -/
theorem SignedCalendarAt.reportWordsOnOriginalSelection : originalFieldReports.1 :=
  originalFieldReports.2

end Diagonal

end BorderVNP
end Computability
end OAI
