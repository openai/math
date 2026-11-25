import OAI.Computability.BorderVNP.DiagonalAcquiredNativeSelection
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedOwnerPair
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacementData
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalRunsAtNext
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSourceCompletion

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta TeamContraction.ProcessorSlots
set_option maxHeartbeats 5000000
set_option maxRecDepth 14000
set_option Elab.async false

/-- Apply the actual prepared runner on the continuation, owner and original
issued cells of its selected native call. The four inputs are read from the
runner itself, so its result retains the original history, candidate and source. -/
private def protectedMeasuredCall : MetaM Expr := do
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
    forallBoundedTelescope (← inferType run) (some 4) fun selection _ => do
      if selection.size != 4 then throwError "expected the continuation, base, owner and issued cells"
      let before := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenPreparationOnNativeNext)
        (parameters.push selection[0]!)
      let prep := mkProj ``Subtype 0 before
      let checked := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.chosenOriginalSourceComplete)
        (parameters.extract 0 i ++ #[selection[0]!, prep] ++ selection.extract 1 4)
      let family ← mkLambdaFVars selection (← inferType checked)
      let handler ← mkLambdaFVars selection checked
      let applySelection := mkConst ``BootedPinStart.PreparedHistoryDecoder.applyNativeSelection [.zero, .zero]
      let input := roster.getAppArgs ++ #[routed, saved, owner, held, family, handler]
      mkLambdaFVars parameters (mkAppN applySelection input)

local elab "measuredGuardProof%" : term => do
  let proof ← protectedMeasuredCall
  let prop ← inferType proof
  let ps := mkSort .zero
  let family := mkLambda `P .default ps (.bvar 0)
  return mkAppN (mkConst ``PSigma.mk [.ofNat 1, .zero]) #[ps, family, prop, proof]

private noncomputable def originalMeasuredCompletion : (P : Prop) ×' P := measuredGuardProof%

/-- The measured native call substantiates each guarded original source on its true prefix. -/
theorem SignedCalendarAt.frozenSubstantiatedAtSources : originalMeasuredCompletion.1 :=
  originalMeasuredCompletion.2

end Diagonal

end BorderVNP
end Computability
end OAI
