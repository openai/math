import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership
import OAI.Computability.BorderVNP.DiagonalReturnedSourceExterior

/-! # The selected writer's original physical exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction

/-- The registered replay and the original all-team tuple appear as separate
indices of the proved native owner statement. Read both indices at the actual
field. The returned comparison reduces only the replay and bare-tuple projections. -/
private def originalSourceAgreement (statement : Bool) : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenOriginalOwnerStatement
    | throwError "expected the original native owner on the selected field"
  forallTelescope shape.value fun fields result => do
    let some event ← whnfUntil result ``PreparationFrame.ReturnedOwnershipAt
      | throwError "expected the actual returned native owner"
    let mut signature := (← getConstInfo ``PreparationFrame.ReturnedOwnershipAt).type
    let mut originInput := none
    let mut exteriorInput := none
    for input in event.getAppArgs do
      if signature.bindingName! == `origin then originInput := some input
      if signature.bindingName! == `exterior then exteriorInput := some input
      signature := signature.bindingBody!
    let some origin := originInput | throwError "the replay has no source"
    let some exterior := exteriorInput | throwError "the original tuple has no exterior"
    let value := mkProj ``Subtype 0 origin
    if statement then mkForallFVars fields (← mkEq value exterior)
    else mkLambdaFVars fields (← mkEqRefl value)

local elab "originalSourceType%" : term => originalSourceAgreement true

/-- Equality of the replay source and the physical exterior of the original
joint native prefix for each issued field. -/
abbrev SignedCalendarAt.OriginalSourceAgreement : Prop := originalSourceType%

/-- The actual source used by the registered writer is the exterior of the
bare tuple reconstructed at this very pin, history, subtotal and report. -/
theorem SignedCalendarAt.issuedSourceExteriorOfCandidates : SignedCalendarAt.OriginalSourceAgreement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalSourceAgreement false)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
