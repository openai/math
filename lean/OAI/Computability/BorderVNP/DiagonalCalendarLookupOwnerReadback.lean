import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalSelectedDeclaredOwnerRead

/-! # The owning team at each declared cell of the attained calendar frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction

/-- Apply the owner read to the actual returned frame. The selected-site operation
shares its fifty parameters with the selected record, including its finite enumerations.
The attained writer's stored owner is its declared-team word at each original cell. -/
private def calendarLookupOwnerRead : MetaM Expr := do
  let lookup ← getConstInfo ``SignedCalendarAt.frozenLookupAt
  let origin := mkConst lookup.name (lookup.levelParams.map Level.param)
  let owner ← getConstInfo ``PreparationFrame.SelectedLookupSites.ownerOnDeclaredCell
  forallTelescopeReducing lookup.type fun inputs shape => do
    let some record ← whnfUntil shape ``PreparationFrame.SelectedLookupSites
      | throwError "expected the original calendar's selected physical frame"
    let selected := mkAppN origin inputs
    -- The owner lemma uses the selected port and inventory universes. Its finite
    -- receiver rows are in Type, the final universe parameter of the selected record.
    let levels := record.getAppFn.constLevels!.take owner.levelParams.length
    let read := mkAppN (mkConst owner.name levels) (record.getAppArgs.push selected)
    let written ← forallTelescope (← whnf (← inferType read)).bindingDomain! fun cell declared => do
      let some (_, physical, _) := declared.eq? | throwError "expected the stored declared owner word"
      mkLambdaFVars cell (← mkEqRefl physical)
    mkLambdaFVars inputs (mkApp read written)

/-- The full original calendar, matching declaration, and cell quantifiers of the
attained native read, taken from its physical frame. -/
elab "calendarLookupOwnerReadType%" : term => do inferType (← calendarLookupOwnerRead)

/-- The native owner words of the attained frame at the selected calendar's original
pin, history, shared subtotal claim, and broadcast. -/
abbrev SignedCalendarAt.LookupOwnerReadback : Prop := calendarLookupOwnerReadType%

/-- Every original cell of every matching route on the attained calendar frame reads
the very team assigned to it by its checked broadcast. -/
theorem SignedCalendarAt.frozenLookupOwnerReadback : SignedCalendarAt.LookupOwnerReadback := by
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.assign (← calendarLookupOwnerRead)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
