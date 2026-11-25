import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHostInstaller

/-! # Source words on the original calendar's joint host memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

/-- Read the source operand of the installed mixed-memory theorem on its original route
and joint owner return. That operand is independent of the subsequently chosen report. -/
private def ownedHostWordView {α : Type} (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let lift ← mkConstWithLevelParams ``SignedCalendarAt.frozenLiftHostReport
  forallTelescopeReducing (← inferType lift) fun xs _ => do
    let names ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes
    let some owner := names.idxOf? `owned | throwError "the host lift must receive an original joint return"
    let some host := xs.back? | throwError "the host lift must receive original source words"
    let raw ← inferType host
    let some words ← whnfUntil raw ``ExternalSew.Fragments.SourceWords
      | throwError "expected the native fragment's source words"
    for x in xs.extract (owner+1) xs.size do
      if words.containsFVar x.fvarId! then
        throwError "the joint host reading cannot depend on a later report input"
    k (xs.extract 0 (owner+1)) words

local elab "ownedHostWords%" : term => do
  ownedHostWordView fun inputs words => mkLambdaFVars inputs words

/-- All fragment source bits are present on their original W-selected owners after the
joint host exchange, at the calendar's input, selector and actual owned return. -/
noncomputable abbrev SignedCalendarAt.OwnedHostWords := ownedHostWords%

private def ownedHostWordEquation : MetaM (Expr × Expr) := do
  ownedHostWordView fun inputs words => do
    let lhs := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.OwnedHostWords) inputs
    return (← mkForallFVars inputs (← mkEq lhs words), ← mkLambdaFVars inputs (← mkEqRefl words))

local elab "ownedHostEquation%" : term => do return (← ownedHostWordEquation).1

/-- The named joint reading uses the original physical state and the native slot coordinates. -/
abbrev SignedCalendarAt.OwnedHostWordIdentity : Prop := ownedHostEquation%

/-- Expand the joint reading to the exact native source operand of the installed report lift. -/
theorem SignedCalendarAt.ownedHostWords_eq : SignedCalendarAt.OwnedHostWordIdentity := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← ownedHostWordEquation).2
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
