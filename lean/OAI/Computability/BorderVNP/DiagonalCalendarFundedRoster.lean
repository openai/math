import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHistory
import OAI.Computability.BorderVNP.DiagonalSupportedFundedRoster

/-! # The funded sparse roster on the original calendar decoder

For every installed calendar column, its original supported preparation runs
with the same routed inputs, rows and report choices as the funded bare launch.
The proof specializes the general supported roster observer to the calendar
decoder, its actual two public budgets and its registered route family.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term
open TeamContraction TeamContraction.ProcessorSlots

/-- Pair the arguments of a fully applied declaration with their binder names.
Looking up the live pin and the decoder indices this way retains the exact
instances and the dependent memory layouts from the two source declarations. -/
private def namedArguments (e : Expr) : MetaM (Array (Name × Expr)) := do
  let some name := e.getAppFn.constName? | throwError "expected a declaration"
  let mut type := (← getConstInfo name).type
  let mut args := #[]
  for x in e.getAppArgs do
    unless type.isForall do throwError "unexpected extra argument to {name}"
    args := args.push (type.bindingName!, x)
    type := type.bindingBody!.instantiate1 x
  return args

private def asApplication (e : Expr) (name : Name) : MetaM Expr := do
  let some applied ← whnfUntil e name | throwError "expected an application of {name}"
  return applied

/-- Use precisely the argument types of the compiled routed input, including
the matrices' network and the receiving history. The right-hand sigma of the
route determines the two dependent indexing families of the public decoder.
The term produced here is a single application of `fundedRouteObserver`. -/
private def frozenRosterProof : MetaM Expr := do
  let route ← mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs
  forallTelescope (← inferType route) fun xs rawEquiv => do
    let values ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
    let some values := values | throwError "the routed input has no matrix family"
    let external := xs.extract (xs.size-3) xs.size
    let original := xs.extract 0 (xs.size-3)
    let sides := (← asApplication rawEquiv ``Equiv).getAppArgs
    let source := (← asApplication sides[0]! ``Sigma).getAppArgs
    let target := (← asApplication sides[1]! ``Sigma).getAppArgs
    let routes ← mkLambdaFVars #[external[1]!] target[0]!
    let reports ← mkLambdaFVars #[external[0]!,external[1]!] target[1]!
    lambdaTelescope source[1]! fun _ parsed => do
      let fields ← namedArguments (← asApplication parsed ``ParsedPreCall)
      let some pin := fields.toList.lookup `live | throwError "missing live wire pin"
      let decoder := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedHistoryDecoder)
        ((xs.extract 0 (values+1)).push pin)
      let sites := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites) (xs.extract 0 values)
      let limit ← mkAppM ``Fin.val #[← mkAppM ``SiteData.limit #[sites]]
      let burst ← mkAppM ``Fin.val #[← mkAppM ``SiteData.burst #[sites]]
      let room := mkApp (mkConst ``Nat.le_refl) burst
      let decoderType ← asApplication (← inferType decoder) ``BootedPinStart.PreparedHistoryDecoder
      let indices ← namedArguments decoderType
      -- The funded observer specializes the generator to the sparse driver.
      let inputs := (indices.filter (fun entry => entry.1 != `gen)).map Prod.snd
      let observer := mkAppN (← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.fundedRouteObserver)
        (inputs ++ #[decoder,limit,burst,room])
      forallBoundedTelescope (← inferType observer) (some 1) fun continuation _ => do
        let routed ← mkLambdaFVars external (mkAppN route xs)
        let observed := mkAppN observer (continuation ++ #[routes,reports,routed])
        mkLambdaFVars (original ++ continuation) observed

local elab "frozenRosterStatement%" : term => do
  inferType (← frozenRosterProof)

/-- The full roster assertion on the frozen supported route, quantified over
the installed calendar, its original source family and its physical returns. -/
abbrev SignedCalendarAt.FundedRoutedRoster : Prop := frozenRosterStatement%

/-- Every funded sparse launch on the original column supplies its own placed
roster and row data on the supported team's physical argument visits. -/
theorem SignedCalendarAt.frozenRosterOnRoute : SignedCalendarAt.FundedRoutedRoster := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← frozenRosterProof)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
