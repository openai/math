import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalCandidateIssuedEmission

/-! # The sparse fragment emitter on the recorded native visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term DiagonalTallyCellReports PackedHistoryCircuit
open private originalOwner from OAI.Computability.BorderVNP.DiagonalAttainedReportOperands

/-- Recover each implicit argument of the fragment emission from the recorded
candidate, the prepared native input and its allocation, and the address calibration. -/
elab (name := issuedFragmentOnRecordedVisit) "issuedFragmentOnRecordedVisit% " candidate:term:max atVisit:term:max worker:term:max
    fresh:term:max destination:term:max complete:term:max caps:term:max
    seed:term:max alloc:term:max bounds:term:max head:term:max : term => do
  let (starts,reached,n) ← originalOwner (← elabTerm atVisit none)
  let explicit ← #[candidate,worker,fresh,destination,complete,caps,seed,alloc,bounds,head].mapM fun t => elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let explicit ← explicit.mapM instantiateMVars
  let explicitNames := #[`actual,`u,`fresh,`destination,`complete,`caps,`seed,`alloc,`bounds,`head]
  let method := ``ReturnedCandidateReports.issuedEmissionOnPrefix
  let source ← getConstInfo method
  forallTelescope source.type fun fields _ => do
    let mut evidence := explicitNames.zip explicit
    evidence := evidence ++ #[ (`n,n), (`U,starts), (`active,reached) ]
    let names ← fields.mapM fun field => field.fvarId!.getUserName
    let mut operands : Array (Expr × Expr) := #[]
    for (sourceParam,patternHead) in #[(`actual,``ReturnedCandidateReports),(`seed,``PreparedReportInput),
        (`alloc,``ReportAllocation),(`bounds,``SignedTaskArena.Layout.FinishAddresses)] do
      let some index := names.idxOf? sourceParam | throwError "missing native parameter {sourceParam}"
      let some observed := evidence.toList.lookup sourceParam | throwError "missing native report operand {sourceParam}"
      let some formal ← whnfUntil (← inferType fields[index]!) patternHead |
        throwError "unexpected signature for {sourceParam}"
      let some real ← whnfUntil (← inferType observed) patternHead |
        throwError "expected the recorded {patternHead}"
      operands := operands ++ formal.getAppArgs.zip real.getAppArgs
    let some countProof := evidence.toList.lookup `complete | throwError "missing output count"
    let countType ← inferType countProof
    let some inequality ← whnfUntil countType ``LE.le | throwError "expected native gate count inequality"
    let sides := inequality.getAppArgs
    let some gates ← whnfUntil sides[sides.size-2]! ``TerminalCells.signedGridOutputCount |
      throwError "missing the recorded output suffix"
    evidence := evidence.push (`suffix,gates.getAppArgs.back!)
    let mut args := #[]
    for i in [:fields.size] do
      let x := fields[i]!
      let name := names[i]!
      if let some value := evidence.toList.lookup name then
        args := args.push value
      else if [`pubAt,`owned,`assigned,`bankAt].contains name then
        let eqn := (← inferType x).replaceFVars (fields.extract 0 i) args
        let some eq ← whnfUntil eqn ``Eq | throwError "expected native equality {name}"
        let xs := eq.getAppArgs
        args := args.push (mkApp2 (mkConst ``Eq.refl eq.getAppFn.constLevels!) xs[0]! xs[1]!)
      else
        let some (_,recorded) := operands.find? (fun p => p.1 == x) |
          throwError "the returned native data did not provide {name}"
        args := args.push recorded
    let some c ← whnfUntil (← inferType explicit[0]!) ``ReturnedCandidateReports |
      throwError "expected authentic candidate reports"
    return ShareCommon.shareCommon (mkAppN (mkConst method c.getAppFn.constLevels!) args)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
