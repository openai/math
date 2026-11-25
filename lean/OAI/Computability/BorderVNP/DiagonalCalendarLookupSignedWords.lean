import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup

/-! # Signed extension words at a returned calendar site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction RoutingISA RoutingISA.Evaluator.SignedPrep PackedHistoryCircuit
open VPVNP.BurstRAM Packing

/-- Moving to the equal planner layout changes only the indicated extension of
the sampled private words. The six witnesses are those of the original row. -/
private theorem signedWordsOnPlanner {w : ℕ} {before after : SignedTaskArena.Layout} {team : ℕ}
    {dir : Directory.Layout} {sampled old : Fin 81 → Word w} {origin edges cells pinned subtotal : ℕ}
    (planner : before = after)
    (returned : sampled = routingExtension (before.extension pinned team subtotal old) dir origin edges cells) :
    ∃ (old : Fin 81 → Word w) (origin edges cells pinned subtotal : ℕ),
      sampled = routingExtension (after.extension pinned team subtotal old) dir origin edges cells := by
  cases planner
  exact ⟨old, origin, edges, cells, pinned, subtotal, returned⟩

private def atHead (e : Expr) (head : Name) : MetaM Expr := do
  let some result ← whnfUntil e head | throwError "expected the original {head}"
  return result

/-- Match the typed inputs of the planner equality against the calendar
variables. Its grid is the grid of the operative execution itself. -/
private def plannerEquality (inputs : Array Expr) : MetaM Expr := do
  let names ← inputs.mapM fun x => x.fvarId!.getUserName
  let some i := names.findIdx? (· == `oper) | throwError "missing the operative calendar"
  let available := (names.zip inputs).push (`grid, mkProj ``FrozenExecutionAt 0 inputs[i]!)
  let rule ← getConstInfo ``SignedCalendarAt.frozenPlannerTask_eq
  let mut signature := rule.type
  let mut args := #[]
  while signature.isForall do
    let name := signature.bindingName!
    let matching := available.filter (fun (key, _) => key.eraseMacroScopes == name.eraseMacroScopes)
    let argument ← if matching.size == 1 then pure matching[0]!.2 else do
      let domain := signature.bindingDomain!.instantiateRev args
      let some (_, x) ← matching.findM? (fun (_, x) => do isDefEq (← inferType x) domain)
        | throwError "missing the planner's typed operand {name}"
      pure x
    args := args.push argument
    signature := signature.bindingBody!
  return mkAppN (← mkConstWithLevelParams rule.name) args

/-- Read the original site certificate first, then read the actual nested
extensions in its `oldWords` equality. This retains its original registers,
directory, address and row counts throughout the change of planner. -/
private def returnedSignedWords : MetaM Expr := do
  let lookup ← getConstInfo ``SignedCalendarAt.frozenLookupAt
  forallTelescope lookup.type fun inputs _ => do
    let site := mkAppN (← mkConstWithLevelParams lookup.name) inputs
    let attained := mkProj ``PreparationFrame.SelectedLookupSites 1 site
    let planner ← plannerEquality inputs
    let change ← atHead (← inferType planner) ``Eq
    forallBoundedTelescope (← inferType attained) (some 2) fun indices _ => do
      let reached := mkAppN attained indices
      let row ← atHead (← inferType reached) ``Exists
      let chosen := mkAppN (mkConst ``Classical.choose_spec row.getAppFn.constLevels!)
        (row.getAppArgs.push reached)
      let seen := mkProj ``CandidateSite.OnReturn 0 (mkProj ``And 0 chosen)
      let words ← atHead (← inferType seen) ``Eq
      let routed ← atHead words.getAppArgs.back! ``routingExtension
      let #[width, entry, directory, origin, edges, cells] := routed.getAppArgs
        | throwError "unexpected operands of the original routing extension"
      let extension ← atHead entry ``SignedTaskArena.Layout.extension
      let #[_, before, pinned, team, subtotal, old] := extension.getAppArgs
        | throwError "unexpected operands of the original signed extension"
      let proof := mkAppN (mkConst ``signedWordsOnPlanner)
        #[width, before, change.getAppArgs.back!, team, directory, words.getAppArgs[1]!,
          old, origin, edges, cells, pinned, subtotal, planner, seen]
      mkLambdaFVars (inputs ++ indices) proof

local elab "returnedSignedWordsType%" : term => do inferType (← returnedSignedWords)

/-- Every exterior and team of the original calendar declaration has the
signed routing words of its actual preparation site. -/
noncomputable abbrev SignedCalendarAt.FrozenLookupSignedWords : Prop := returnedSignedWordsType%

/-- The original returned site supplies all six operands of the native signed
writer on the actual planner layout. -/
theorem SignedCalendarAt.frozenLookupSignedWords : SignedCalendarAt.FrozenLookupSignedWords := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← returnedSignedWords)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
