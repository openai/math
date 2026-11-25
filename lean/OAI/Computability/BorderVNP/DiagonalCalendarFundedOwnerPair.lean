import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedAtRoutes
import OAI.Computability.BorderVNP.DiagonalOwnerBaseOnFundedPackets

/-! # The native owner table on the funded input of the calibrated reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

private def ownerAtRecordedPackets : MetaM Expr := do
  let .defnInfo recorded ← getConstInfo ``SignedCalendarAt.frozenSuppliedAtRoutes
    | throwError "expected the registered funded packet map"
  lambdaTelescope recorded.value fun parameters provided => do
    let some native ← whnfUntil provided ``BootedPinStart.PreparedHistoryDecoder.suppliedPacketsAtRoute
      | throwError "expected the selected packet map on the native source roster"
    let owner ← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.ownerBaseOnFundedPackets
    mkLambdaFVars parameters (mkAppN owner native.getAppArgs)

local elab "fundedOwnerRequest%" : term => do inferType (← ownerAtRecordedPackets)

/-- The native calls use the very sparse sources produced by the selected
reader on this funding, and the resulting owner tables use their continuation. -/
noncomputable abbrev SignedCalendarAt.FundedOwnerRequest : Type _ := fundedOwnerRequest%

/-- The public pre-call address and the owner agreement for the calls that ran
from the jointly funded packet on each genuine checked candidate. -/
noncomputable def SignedCalendarAt.frozenBaseOwnerOfFundedCandidates : SignedCalendarAt.FundedOwnerRequest := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← ownerAtRecordedPackets)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
