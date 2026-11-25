import OAI.Computability.BorderVNP.DiagonalCalendarExecutionOnStoredOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarEarnedOriginalReportPoints
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReports

/-! # The complete physical execution at each selected original pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term
set_option maxHeartbeats 9000000
set_option maxRecDepth 24000
set_option cleanup.letToHave false

private def headerSlot (parameters : Array Expr) : MetaM (Option Nat) :=
  parameters.findIdxM? fun x => do
    let ty := (← inferType x).consumeMData
    unless ty.isAppOfArity ``Fact 1 do return false
    let condition := ty.appArg!.consumeMData
    return condition.isAppOf ``LE.le || condition.isAppOf ``Nat.le

private def operatorHeaderSlot (op : Expr) : MetaM (Option Nat) := do
  forallBoundedTelescope (← inferType op) (some 52) (whnfType := true) fun xs _ => headerSlot xs

local elab "runAtOriginalPin%" : term => do
  let raw ← mkConstWithLevelParams ``SignedCalendarAt.frozenLookupReports
  let exec ← mkConstWithLevelParams ``SignedCalendarAt.executionOnStoredOriginalReports
  let earn ← mkConstWithLevelParams ``SignedCalendarAt.earnedStoreOnOriginalReports
  let earnedSlot ← operatorHeaderSlot earn
  let execSlot ← operatorHeaderSlot exec
  forallBoundedTelescope (← inferType raw) (some 52) (whnfType:=true) fun xs _ => do
    let tail ← (xs.extract 50 52).mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes
    unless tail == #[`values,`h] do throwError "expected the original table and pin"
    let observation := mkAppN raw xs
    let some sourceSlot ← headerSlot xs | throwError "missing original reader header bound"
    let bound := xs[sourceSlot]!
    let ordinary := xs.extract 0 sourceSlot ++ xs.extract (sourceSlot+1) xs.size
    let calibratedInputs (slot : Option Nat) := match slot with
      | none => ordinary
      | some index => ordinary.extract 0 index ++ #[bound] ++ ordinary.extract index ordinary.size
    let actual := mkAppN earn ((calibratedInputs earnedSlot).push observation)
    let pin := mkAppN exec (((calibratedInputs execSlot).push observation).push actual)
    let ctx ← instantiateLCtxMVars (← getLCtx)
    let .ok result := Kernel.check (← getEnv) ctx pin
      | throwError "the proved original reports do not fit this physical pin"
    unless (← whnfUntil result ``ChosenReader.WiredPinExecution).isSome do
      throwError "expected an unconditional wired pin execution"
    let (claim,program) := ShareCommon.shareCommon' (← mkForallFVars xs result, ← mkLambdaFVars xs pin)
    let level ← getLevel claim
    let sort := mkSort level
    return mkAppN (mkConst ``PSigma.mk [level.succ,level])
      #[sort,mkLambda `Result .default sort (mkBVar 0),claim,program]

set_option Elab.async false in
private noncomputable def originalProgram : (Result : Type 1) ×' Result := runAtOriginalPin%

/-- The original machine supplies every observation used by the native column at this pin. -/
noncomputable def SignedCalendarAt.frozenRun : originalProgram.1 := originalProgram.2

end Diagonal

end BorderVNP
end Computability
end OAI
