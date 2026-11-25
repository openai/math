import OAI.Computability.BorderVNP.DiagonalSelectedSourceReadIssuance

/-! # Reading a selected return at the planner layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction RoutingISA.Evaluator.SignedPrep

/-- Transport the old extension word (field 35) through the installed layout
equality. Every other field, including the final four witnesses, comes from the
same return. -/
private def snapshotAtPlanner (wanted observed returned plannerEq : Expr) : MetaM Expr := do
  let fields := observed.getAppArgs
  unless observed.isAppOfArity ``CandidateSite.OnReturn 50 do
    throwError "expected the original physical return"

  let mut goal := wanted
  let mut constructors := #[]
  for witness in fields.extract 46 50 do
    let some ex ← whnfUntil goal ``Exists | throwError "expected four physical snapshot witnesses"
    let #[type,predicate] := ex.getAppArgs | throwError "unexpected snapshot existential"
    constructors := constructors.push (mkApp3 (mkConst ``Exists.intro ex.getAppFn.constLevels!) type predicate witness)
    goal := predicate.beta #[witness]

  let some target ← whnfUntil goal ``CandidateSite.OnReturn | throwError "expected the planner return"
  let anchor ← mkFreshExprMVar (mkConst ``True)
  let old := fields[35]!
  let change ← anchor.mvarId!.rewrite old plannerEq
  unless change.mvarIds.isEmpty do throwError "expected a fully applied layout equality"
  let family ← withLocalDeclD `old (← inferType old) fun word =>
    mkLambdaFVars #[word] (mkAppN observed.getAppFn (fields.set! 35 word))
  let same ← mkCongrArg family change.eqProof
  if target.hasMVar then
    unless ← isDefEq (mkAppN observed.getAppFn (fields.set! 35 change.eNew)) target do
      throwError "the rewritten return does not identify the planner snapshot"
  let transported := mkApp4 (mkConst ``Eq.mp [.zero]) observed target same returned
  return constructors.foldr (fun ctor proof => mkApp ctor proof) transported

/-- Given selected lookup sites and the calendar's layout equality, supply the
actual register bank, memory, and two costs required by their planner snapshot. -/
elab "actualSnapshotWithPlannerEq% " chosen:term:max ", " alignment:term:max : term <= wanted => do
  let chosen ← elabTerm chosen none
  let plannerEq ← elabTerm alignment none
  let some sites ← whnfUntil (← inferType chosen) ``PreparationFrame.SelectedLookupSites
    | throwError "expected the selected lookup sites"
  let evidence := sites.getAppArgs.back!
  forallBoundedTelescope wanted (some 2) fun point goal => do
    unless point.size == 2 do throwError "expected an exterior and a team"
    let site := mkAppN (mkProj ``PreparationFrame.SelectedLookupSites 0 chosen) point
    let attained := mkAppN (mkProj ``PreparationFrame.SelectedLookupSites 1 chosen) point
    let some ex ← whnfUntil (mkAppN evidence (point.push site)) ``Exists
      | throwError "expected the trace attained at the selected site"
    let #[traceType,predicate] := ex.getAppArgs | throwError "unexpected attained trace"
    let levels := ex.getAppFn.constLevels!
    withLetDecl `attained ex attained fun found => do
      let witness := mkApp3 (mkConst ``Classical.choose levels) traceType predicate found
      withLetDecl `trace traceType witness fun trace => do
        let some both ← whnfUntil (predicate.beta #[trace]) ``And
          | throwError "expected the selected return and its accompanying observations"
        let #[first,rest] := both.getAppArgs | throwError "unexpected trace observations"
        let some observed ← whnfUntil first ``CandidateSite.OnReturn | throwError "expected the attained physical return"
        let facts := mkApp3 (mkConst ``Classical.choose_spec levels) traceType predicate found
        let returned := mkApp3 (mkConst ``And.left) first rest facts
        let result ← snapshotAtPlanner goal observed returned plannerEq
        mkLambdaFVars point (← mkLetFVars #[found,trace] result (generalizeNondepLet := false))

end Diagonal

end BorderVNP
end Computability
end OAI
