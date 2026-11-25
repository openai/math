import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalRoutedRosterIssuance
import OAI.Computability.BorderVNP.DiagonalCalendarSparsePlacementEvidence

/-! # Native candidate issuance on the frozen calendar's original route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta TeamContraction.ProcessorSlots

/-- Apply the issued-cell operation to precisely the operands defining the
calendar's original routing domain. At the retained cut, keep the frozen
placement of those same native teams. The resulting expression is elaborated
and checked by the kernel at the original calendar telescope. -/
def originalIssuanceTerm (keep : Bool) : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected route telescope"
  forallTelescope shape.value fun binders endType => do
    let some atRoutes ← whnfUntil endType ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "the selected route family does not end on the native source roster"
    let input := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) binders
    let args := atRoutes.getAppArgs.push input
    let result ← if keep then do
        let some i ← binders.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `entries)
          | throwError "expected the original directory of entries"
        let saved := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSparseSaved)
          (binders.extract 0 i)
        let operation ← getConstInfo ``BootedPinStart.PreparedHistoryDecoder.heldAtRoutes
        pure (mkAppN (mkConst operation.name (operation.levelParams.map (fun _ => Level.zero))) (args.push saved))
      else pure (mkAppN (← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.candidateAtRoutes) args)
    mkLambdaFVars binders result

local elab "calendarCandidateIssuanceType%" : term => do inferType (← originalIssuanceTerm false)

/-- The native issuing operations indexed by the frozen reader's real candidates. -/
noncomputable abbrev SignedCalendarAt.FrozenCandidateIssuance : Type _ := calendarCandidateIssuanceType%

/-- On the decoded original route, the candidate determines its genuine
issued inputs, owner directory and retained sparse source. -/
noncomputable def SignedCalendarAt.frozenIssuedDataOfCandidates : SignedCalendarAt.FrozenCandidateIssuance := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalIssuanceTerm false)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
