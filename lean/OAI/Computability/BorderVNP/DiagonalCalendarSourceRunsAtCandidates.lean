import OAI.Computability.BorderVNP.DiagonalAcquiredNativeSelection
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedOwnerPair
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacementData
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalRunsAtNext

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta TeamContraction.ProcessorSlots
set_option maxHeartbeats 5000000
set_option maxRecDepth 14000
set_option Elab.async false
set_option cleanup.letToHave false

/-- Give each original argument the type of its position in the prepared
runner before supplying the next argument. The kernel verifies all four
assignments on the selected call. -/
private def supplyNativeInputs (operation : Expr) (original chosen : Array Expr) :
    List (Name × Expr) → MetaM Expr
  | [] => pure (mkAppN operation chosen)
  | (name, value) :: rest => do
    let earlier := original.extract 0 chosen.size
    let type := (← inferType original[chosen.size]!).replaceFVars earlier chosen
    withLetDecl name type value fun selected => do
      let body ← supplyNativeInputs operation original (chosen.push selected) rest
      mkLetFVars #[selected] body (generalizeNondepLet := false)

/-- Apply the actual prepared runner on the continuation, owner and original
issued cells of its selected native call. The four inputs are read from the
runner itself, so its result retains the original history, candidate and source. -/
private def runOnMeasuredCall : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the selected calendar routes"
  forallTelescope shape.value fun parameters routes => do
    let some roster ← whnfUntil routes ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the selected source roster"
    let some i ← parameters.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `entries)
      | throwError "expected the selected calendar entries"
    let routed := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) parameters
    let ownerInfo ← getConstInfo ``SignedCalendarAt.frozenBaseOwnerOfCandidates
    let owner := mkAppN (mkConst ownerInfo.name (ownerInfo.levelParams.map (fun _ => .zero))) parameters
    let held := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedReadbackOfCandidates) parameters
    let saved := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSparseSaved) (parameters.extract 0 i)
    let run := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenOriginalRunsAtPreparedNext) parameters
    let parts := mkConst ``BootedPinStart.PreparedHistoryDecoder.partsOfOwnerAndHeld [.zero]
    let originalParts := mkAppN parts (roster.getAppArgs ++ #[routed, saved, owner, held])
    forallBoundedTelescope (← inferType originalParts) (some 2) fun inputs _ => do
      if inputs.size != 2 then throwError "expected an original acquisition and its native calls"
      let calls := inputs[1]!
      let some native ← whnfUntil (← inferType calls) ``BootedPinStart.NativeCalls
        | throwError "expected the calls from this sparse acquisition"
      let selected := mkAppN (← mkConstWithLevelParams ``BootedPinStart.nativeNext)
        (native.getAppArgs.push calls)
      let values := mkAppN originalParts inputs
      withLetDecl `acquiredFields (← inferType values) values fun fields => do
        let base := mkProj ``Sigma 0 fields
        let tail := mkProj ``Sigma 1 fields
        let owners := mkProj ``PLift 0 (mkProj ``Prod 0 tail)
        let issued := mkProj ``Prod 1 tail
        let result ← forallBoundedTelescope (← inferType run) (some 4) fun formals _ => do
          if formals.size != 4 then throwError "expected the original continuation, base, owners and issued cells"
          supplyNativeInputs run formals #[] [(`nativeNext,selected),(`base,base),
            (`ownerTable,owners),(`issued,issued)]
        let shared ← mkLetFVars #[fields] result (generalizeNondepLet := false)
        mkLambdaFVars (parameters ++ inputs) shared

/-- Package the run at the actual acquired calls with its result type. -/
local elab "nativeSelectionPair%" : term => do
  let nativeRun ← runOnMeasuredCall
  let type ← inferType nativeRun
  let universeOfTypes := mkSort (.ofNat 2)
  let id := mkLambda `A BinderInfo.default universeOfTypes (.bvar 0)
  return mkAppN (mkConst ``Sigma.mk [.ofNat 2, .ofNat 1]) #[universeOfTypes, id, type, nativeRun]

private noncomputable def selectedSourceOperation : (A : Type 1) × A := nativeSelectionPair%

/-- Every acquired calendar input gives the actual prepared runs on all returning original sources. -/
noncomputable def SignedCalendarAt.frozenOriginalRunsOfCandidates : selectedSourceOperation.1 :=
  selectedSourceOperation.2

end Diagonal

end BorderVNP
end Computability
end OAI
