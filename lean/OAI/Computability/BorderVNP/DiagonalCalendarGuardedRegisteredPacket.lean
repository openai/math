import OAI.Computability.BorderVNP.DiagonalCalendarSubstantiatedRegistrations
import OAI.Computability.BorderVNP.DiagonalCalendarCandidatePackets
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateReader
import OAI.Computability.BorderVNP.DiagonalCalendarFeasiblePost

/-! # Signed native packets from the registered original source

The cell and row data in a registered completion determine the arguments of the
guarded packet rule. The original charged reader and the completion use the
same native continuation. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000

open Lean Meta Elab Term in
private partial def receiptHead (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => receiptHead (body.instantiate1 value)
  | term =>
    let reduced := term.headBeta
    if reduced == term then term else receiptHead reduced

open Lean Meta Elab Term in
private def candidateParameters (count : Nat) (type : Expr) : MetaM (Array Name) := do
  let mut rest := type
  let mut names := #[]
  for _ in [:count] do
    let .forallE name _ body _ := receiptHead rest | throwError "unexpected prepared row parameters"
    names := names.push name
    rest := body
  return names


private def originalInputs (witness : Expr) : MetaM (Array Expr) := do
  let completion := receiptHead witness.getAppArgs[0]!
  unless completion.isAppOf ``BorderVNP.RoutingISA.Evaluator.UncheckedCandidate.Completion do
    throwError "expected a native row completion"
  let receipt := completion.getAppArgs
  let recorded := receiptHead receipt[receipt.size-2]!
  let some candidate ← withTransparency .all <|
      whnfUntil recorded ``BorderVNP.RoutingISA.Evaluator.PreparedCellRows.candidate
    | throwError "unexpected original candidate {recorded.getAppFn.constName?}"
  let args := candidate.getAppArgs
  let names ← candidateParameters args.size (← getConstInfo ``BorderVNP.RoutingISA.Evaluator.PreparedCellRows.candidate).type
  let argument := fun (key : Name) => do
    let some index := names.idxOf? key | throwError "actual candidate has no {key} field"
    pure args[index]!
  let .lam _ _ body _ := receiptHead witness.getAppArgs[1]! | throwError "missing protected source items"
  let rowsAndProtection := receiptHead body
  unless rowsAndProtection.isAppOfArity ``And 2 do throwError "missing original row matrix"
  let rowEq := receiptHead rowsAndProtection.getAppArgs[0]!
  unless rowEq.isAppOfArity ``Eq 3 do throwError "missing recovered counts"
  let counts := rowEq.getAppArgs.back!
  unless !counts.hasLooseBVar 0 do throwError "recovered counts depend on the completion"
  let protectedAndTotal := receiptHead rowsAndProtection.getAppArgs[1]!
  unless protectedAndTotal.isAppOfArity ``And 2 do throwError "missing protection and true totals"
  let .forallE coord domain coordinate info := receiptHead protectedAndTotal.getAppArgs.back!
    | throwError "missing column coordinate"
  let totalEq := receiptHead coordinate
  unless totalEq.isAppOfArity ``Eq 3 do throwError "missing signed term total"
  let column := Expr.lam coord domain totalEq.getAppArgs.back! info
  unless !column.hasLooseBVar 0 do throwError "true column depends on the completion"
  return #[← argument `J, ← argument `banks, ← argument `i, ← argument `q, ← argument `v,
    args.back!, receipt.back!, counts.lowerLooseBVars 1 1, column.lowerLooseBVars 1 1]

/-- Build the actual original guarded packet from the real registered operation of this native continuation. -/
private def registeredPacket : MetaM (Expr × Expr) := do
  let hName := ``SignedCalendarAt.frozenSubstantiatedAtRegisteredSources
  let info ← getConstInfo hName
  forallBoundedTelescope info.type (some 60) (whnfType:=true) fun inputs remaining => do
    unless inputs.size == 60 do throwError "expected the registered 60-field original receipt"
    let registration := (← inferType inputs[59]!).consumeMData
    let rule ← match registration with
      | .proj _ 1 concrete => pure concrete
      | other =>
        unless other.getAppFn.constName?.any (·.toString.endsWith ".OriginalReportRule.runs") do
          throwError "the actual receipt has no registration"
        pure other.getAppArgs.back!
    unless rule.isAppOfArity ``SignedCalendarAt.frozenRegistrationAtNativeNext 57 do
      throwError "the source has lost the registered native continuation"
    let source := rule.getAppArgs
    for i in [:3] do
      unless ← isDefEq source[54+i]! inputs[55+i]! do throwError "mismatched registered original coordinate"
    let original := mkAppN (← mkConstWithLevelParams hName) inputs
    let some witness ← whnfUntil remaining ``Exists | throwError "missing registered completion"
    let actual ← originalInputs witness
    unless actual.size==9 do throwError "missing original guarded data"
    for i in [:3] do
      unless ← isDefEq actual[2+i]! inputs[55+i]! do throwError "mismatched original candidate coordinates"
    let some pair ← whnfUntil (← inferType inputs[57]!) ``Prod | throwError "the original private assignment is not a pair"
    let privateFamily ← mkLambdaFVars #[inputs[56]!] pair.getAppArgs[1]!
    let feasibility := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenDeployedFeasiblePost) (source.extract 0 49)
    forallBoundedTelescope (← inferType feasibility) (some 1) (whnfType:=true) fun rates _ => do
      let feasible := mkAppN feasibility rates
      let gStart := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenGuardedPacketsAtCandidateNext) (source.extract 0 50)
      let (sizes, _, remainingG) ← forallMetaBoundedTelescope (← inferType gStart) 13
      let .forallE _ expected _ _ ← whnf remainingG | throwError "missing deployed post feasibility"
      unless ← isDefEq expected (← inferType feasible) do throwError "original post and guarded dimensions disagree"
      let shape ← sizes.mapM instantiateMVars
      unless shape.size==13 && shape.all (!·.hasMVar) do throwError "unresolved native guarded geometry"
      let g := mkAppN gStart ((shape.push feasible) ++ source.extract 50 54 ++ #[privateFamily])
      let k := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenKeptOfCandidatePost) (source.extract 0 54)
      forallBoundedTelescope (← inferType k) (some 8) (whnfType:=true) fun costs _ => do
        unless costs.size==8 do throwError "expected the selected seven charge coordinates and post receipt"
        let kept := mkAppN k costs
        let combined := mkAppN g (actual ++ #[original,kept])
        let result ← inferType combined
        let some conclusion ← whnfUntil result ``Exists | throwError "the recorded packet is incomplete"
        unless conclusion.getAppArgs[0]!.getAppFn.constName? ==
            witness.getAppArgs[0]!.getAppFn.constName? do throwError "the native completion head changed"
        let args := inputs ++ rates ++ costs
        let claim ← mkForallFVars args result
        let proof ← mkLambdaFVars args combined
        return ShareCommon.shareCommon' (claim, proof)

local elab "registeredNativeReturn%" : term => do
  let (claim, proof) ← registeredPacket
  let p := mkSort .zero
  let id := mkLambda `P BinderInfo.default p (.bvar 0)
  return mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[p,id,claim,proof]

set_option Elab.async false in
private noncomputable def recordedNativeGuard : (P : Prop) ×' P := registeredNativeReturn%

/-- The protected registered runs yield a completed packet with the original signed
column on the same raw pin, history, private assignment and native continuation. -/
theorem SignedCalendarAt.guardedRegisteredPacket : recordedNativeGuard.1 := recordedNativeGuard.2
end Diagonal

end BorderVNP
end Computability
end OAI
