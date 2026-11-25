import OAI.Computability.BorderVNP.DiagonalCalendarFundedRegisteredExecution
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredRunsAtClock
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedPostClock

/-! # The original measured registrations and writer charges realize the funded execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal
open Lean Meta Elab Term

set_option maxHeartbeats 8500000
set_option maxRecDepth 16000

/-- Read the source observations at the selected measured continuation and map its issued writer
requests to the actual retained register of team zero. -/
private def executionOnObservedReports : MetaM (Expr × Expr) := do
  let executionName := ``SignedCalendarAt.fundedRegisteredExecution
  let info ← getConstInfo executionName
  forallBoundedTelescope info.type (some 56) (whnfType:=true) fun args _ => do
    let n := args.size
    let last := args.extract (n-5) n
    let names ← last.mapM fun v => do pure (← v.fvarId!.getDecl).userName.eraseMacroScopes
    unless names==#[`valid,`measured,`funded,`registered,`charged] do throwError "unexpected native receipt arguments {names}"
    let valid := last[0]!
    let measured := last[1]!
    let funded := last[2]!
    let nativeRegistered := last[3]!
    let nativeCharges := last[4]!
    let prefixArgs := args.extract 0 (n-2)
    let calInputs ← forallTelescope (← inferType valid) fun _ clause => do
      let some checked ← withTransparency .all <| whnfUntil clause ``SignedCalendarAt.FrozenRouteChecks
        | throwError "missing original checked field inputs"
      let pars := checked.getAppArgs
      return (pars.extract 0 (pars.size-3)).push valid
    let supplied := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSuppliedAtRoutes) (calInputs.push funded)
    let sparse := mkProj ``Prod 1 supplied
    let agreement := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRegisteredRunsAtMeasuredSelection)
      (calInputs ++ #[measured,sparse])
    let originalRegs ← inferType nativeRegistered
    let (reported, castReport) ← forallBoundedTelescope originalRegs (some 3) (whnfType:=true) fun xyz target => do
      let same := mkAppN agreement xyz
      let some proposition ← withTransparency .all <| whnfUntil (← inferType same) ``Eq
        | throwError "the measured registration was not restored"
      let endpoints := proposition.getAppArgs
      let ctx ← instantiateLCtxMVars (← getLCtx)
      let .ok true := Kernel.isDefEq (← getEnv) ctx (← instantiateMVars endpoints[2]!)
          (← instantiateMVars target) | throwError "the measured registration refers to another physical return"
      let input ← mkForallFVars xyz endpoints[1]!
      let cast ← withLocalDeclD `witness endpoints[1]! fun witness => do
        let result := mkAppN (mkConst ``Eq.mp [.zero]) #[endpoints[1]!,endpoints[2]!,same,witness]
        mkLambdaFVars (xyz.push witness) result
      return (input, cast)
    let some oi ← prefixArgs.findIdxM? (fun x => do pure ((← x.fvarId!.getDecl).userName.eraseMacroScopes == `oper))
      | throwError "the funded program has no operative calendar"
    let rate ← mkAppM ``FrozenExecutionAt.post #[prefixArgs[oi]!]
    let post := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.issuedClockOfPostRequests)
      (calInputs.pop ++ #[rate,valid])
    let .forallE _ requestsType _ _ ← whnf (← inferType post) | throwError "the original writer has no registered request"
    let column := mkAppN (← mkConstWithLevelParams executionName) prefixArgs
    withLocalDeclD `reports reported fun reports =>
      withLocalDeclD `requests requestsType fun requests => do
        let registered ← forallBoundedTelescope originalRegs (some 3) (whnfType:=true) fun xyz _ => do
          let receipt := (mkAppN castReport (xyz.push (mkAppN reports xyz))).headBeta
          mkLambdaFVars xyz receipt
        let originalPost := mkApp post requests
        let kept ← forallBoundedTelescope (← inferType nativeCharges) (some 1) (whnfType:=true) fun field _ => do
          let after := mkAppN originalPost field
          let .forallE _ team _ _ ← whnf (← inferType after) | throwError "missing original team coordinate"
          let zero ← mkAppOptM ``OfNat.ofNat #[some team,some (mkNatLit 0),none]
          mkLambdaFVars field (mkApp after zero)
        let native := mkAppN column #[registered,kept]
        let ty ← inferType native
        let xs := prefixArgs ++ #[reports,requests]
        let conclusion ← mkForallFVars xs ty
        let proof ← mkLambdaFVars xs native
        unless !proof.hasFVar && !conclusion.hasFVar do throwError "an independent registered source remained"
        return ShareCommon.shareCommon' (conclusion,proof)

local elab "observedRegisteredExecution%" : term => do
  let (claim,execution) ← executionOnObservedReports
  let level ← getLevel claim
  let resultSort := mkSort level
  let id := mkLambda `Result .default resultSort (mkBVar 0)
  return mkAppN (mkConst ``PSigma.mk [level.succ,level]) #[resultSort,id,claim,execution]

set_option Elab.async false in
private noncomputable def observedProgram : (Result : Type 1) ×' Result := observedRegisteredExecution%

/-- The registered source reports at the measured continuation and the actual writer requests
on the selected fields furnish the original wired pin execution. -/
noncomputable def SignedCalendarAt.fundedExecutionAtReportedPost : observedProgram.1 := observedProgram.2

end Diagonal

end BorderVNP
end Computability
end OAI
