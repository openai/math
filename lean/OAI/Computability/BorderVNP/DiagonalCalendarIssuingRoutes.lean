import OAI.Computability.BorderVNP.DiagonalIssuerRouteDomain
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoster
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs

/-! # The original routed inputs at the calendar's issuing roster -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term
open TeamContraction TeamContraction.ProcessorSlots

private def appliedAt (type : Expr) (name : Name) : MetaM Expr := do
  let some app ← whnfUntil type name | throwError "expected an application of {name}"
  return app

private def parametersOf (app : Expr) : MetaM (Array (Name × Expr)) := do
  let some name := app.getAppFn.constName? | throwError "expected a declaration"
  let mut type := (← getConstInfo name).type
  let mut fields := #[]
  for arg in app.getAppArgs do
    fields := fields.push (type.bindingName!,arg)
    type := type.bindingBody!.instantiate1 arg
  return fields

/-- Use the original input declaration's telescope to keep its matrix family,
physical address types and live pin. Its last three binders are precisely the
raw input, history and claim of the native roster's route. -/
local elab "calendarRosterDomain%" : term => do
  let raw ← mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs
  forallTelescope (← inferType raw) fun xs equiv => do
    let some mv ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values) |
      throwError "missing source matrices"
    let static := xs.extract 0 mv
    let withMatrices := xs.extract 0 (mv+1)
    let original := xs.extract 0 (xs.size-3)
    let pair := (← appliedAt equiv ``Equiv).getAppArgs
    let source := (← appliedAt pair[0]! ``Sigma).getAppArgs
    lambdaTelescope source[1]! fun _ parsed => do
      let fields ← parametersOf (← appliedAt parsed ``ParsedPreCall)
      let some pin := fields.toList.lookup `live | throwError "missing live native pin"
      let decoder := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedHistoryDecoder)
        (withMatrices.push pin)
      let core := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingCore) withMatrices
      let roster := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoster) withMatrices
      let sites := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSites) static
      let task := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenTask) static
      let limit ← mkAppM ``Fin.val #[← mkAppM ``SiteData.limit #[sites]]
      let burst ← mkAppM ``Fin.val #[← mkAppM ``SiteData.burst #[sites]]
      let room := mkApp (mkConst ``Nat.le_refl) burst
      let base ← mkAppM ``DiagonalTallyAllocation.BeforeTasks.limit
        #[← mkAppM ``RoutingISA.SignedTaskArena.Layout.before #[task]]
      let decoderFields ← parametersOf (← appliedAt (← inferType decoder) ``BootedPinStart.PreparedHistoryDecoder)
      let decoderArgs := (decoderFields.filter (fun field => field.1 != `gen)).map Prod.snd
      let rosterFields ← parametersOf (← appliedAt (← inferType roster) ``BootedPinStart.SourceRoster)
      -- These are the network dimension, parameters, graph family and its cell count.
      let network := (rosterFields.extract (rosterFields.findIdx (·.1 == `D))
        (rosterFields.findIdx (·.1 == `core))).map Prod.snd
      let args := decoderArgs ++ #[decoder,limit,burst,room] ++ network ++ #[core,roster,base]
      let input := mkAppN (← mkConstWithLevelParams ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes) args
      mkForallFVars original input

/-- The family of physical input types for the calendar issuer, with its installed
site budgets, original core rows, roster and task limit. -/
abbrev SignedCalendarAt.FrozenIssuingRoutes : Type _ := calendarRosterDomain%

/-- The recorded routing equivalence, viewed at the typed first argument of
the issued decoder built from this calendar's original core and source roster. -/
noncomputable abbrev SignedCalendarAt.frozenIssuingRoutes : SignedCalendarAt.FrozenIssuingRoutes := by
  run_tac
    let input ← Lean.mkConstWithLevelParams ``SignedCalendarAt.frozenRoutedInputs
    (← Lean.Elab.Tactic.getMainGoal).assign input
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
