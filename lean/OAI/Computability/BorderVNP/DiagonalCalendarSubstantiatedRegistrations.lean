import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationAtNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRunsAtCandidates
import OAI.Computability.BorderVNP.DiagonalCalendarSubstantiatedSources

/-! # Completion from the original registered reports at the selected native calls

The reported runs and the signed completion use the same original source, subtotal and team.
The kernel checks their common simultaneous starting exterior, every dependent prefix, and
the complete tape of offered reports at the actual guarded route. -/

namespace OAI
namespace Computability
namespace BorderVNP

open Lean Meta Elab Command
namespace Diagonal

set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

private def registeredCompletion : MetaM (Expr × Expr) := do
  let hName := ``SignedCalendarAt.frozenSubstantiatedAtSources
  let original := ``SignedCalendarAt.frozenOriginalRunsAtPreparedNext
  let info ← getConstInfo hName
  -- These binders end at the guard on the original route. The final argument is its source run.
  forallBoundedTelescope info.type (some 59) (whnfType:=true) fun inputs remaining => do
    unless inputs.size==59 do throwError "expected the cal inputs, native calls and original guarded route"
    let originalCall := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenOriginalRunsOfCandidates) inputs.pop
    let some concrete ← whnfUntil originalCall original |
      throwError "the acquired source no longer applies the selected prepared runner"
    let actual := concrete.getAppArgs
    unless actual.size==60 do throwError "expected the common calendar and its six selected source fields"
    -- The registered rule uses the joint native continuation plus raw/history/route.
    let select := actual.extract 0 54 ++ actual.extract 57 60
    let rule := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRegistrationAtNativeNext) select
    let some ruleName := (← inferType rule).getAppFn.constName? | throwError "expected an original report rule"
    let runs := mkProj ruleName 1 rule
    let .forallE _ source _ _ ← whnf remaining | throwError "the signed completion has no original source"
    withLocalDeclD `registered runs fun certificate => do
      let supply ← forallBoundedTelescope source (some 3) (whnfType:=true) fun coordinates wanted => do
        unless coordinates.size==3 do throwError "expected the source report, subtotal and original team"
        -- The actual registered value has the original prefix predicate on this very report.
        -- Preserve it as a proof term, so the kernel checks the two physical presentations.
        let reported := mkAppN certificate coordinates
        mkLambdaFVars coordinates (← mkExpectedTypeHint reported wanted)
      let completion := mkApp (mkAppN (← mkConstWithLevelParams hName) inputs)
        (← mkExpectedTypeHint supply source)
      let parameters := inputs.push certificate
      return (← mkForallFVars parameters (← inferType completion), ← mkLambdaFVars parameters completion)

/-- Retain the source-dependent original completion as one proof at its given proposition. -/
local elab "protectedForRegisteredSources%" : term => do
  let (claim,body) ← registeredCompletion
  let propositions := mkSort .zero
  let identity := mkLambda `P BinderInfo.default propositions (.bvar 0)
  return mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[propositions,identity,claim,body]

private noncomputable def originalRegisteredCompletion : (P : Prop) ×' P := protectedForRegisteredSources%

/-- The actual reports registered at the selected native calls give the protected signed completion
with the sum of its original private tallies in every parameter. -/
theorem SignedCalendarAt.frozenSubstantiatedAtRegisteredSources : originalRegisteredCompletion.1 :=
  originalRegisteredCompletion.2

end Diagonal

end BorderVNP
end Computability
end OAI
