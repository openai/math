import OAI.Computability.BorderVNP.DiagonalCalendarIssuingRoutes
import OAI.Computability.BorderVNP.DiagonalSuppliedAtRosterRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarSparsePlacementEvidence

/-! # Original funded packets at the calendar's attained route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction.ProcessorSlots

private def originalPacketRouteTerm : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.FrozenIssuingRoutes
    | throwError "expected the calendar route telescope"
  forallTelescope shape.value fun params endType => do
    let some domain ← whnfUntil endType ``BootedPinStart.PreparedHistoryDecoder.RosterRoutes
      | throwError "expected the route of the original issuer"
    let route := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuingRoutes) params
    let names ← params.mapM fun x => x.fvarId!.getUserName
    let pos := names.findIdx (· == `values)
    if pos ≥ params.size then throwError "expected the calendar tables parameter"
    let directory := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedDirectory)
      (params.extract 0 (pos+1))
    -- The key, slot and number of real cells come from this same directory.
    let sorts ← forallTelescope (← inferType directory) fun hs output => do
      let some dir ← whnfUntil output ``CellPacketGeometry.SiteWords.Directory
        | throwError "expected the indexed original directory"
      let args := dir.getAppArgs
      let some count ← whnfUntil args[2]! ``Nat.succ
        | throwError "expected the spare-cell extent"
      pure #[← mkLambdaFVars hs args[0]!, ← mkLambdaFVars hs args[1]!,
        ← mkLambdaFVars hs count.getAppArgs[0]!]
    let operation ← getConstInfo ``BootedPinStart.PreparedHistoryDecoder.suppliedPacketsAtRoute
    let fn := mkConst operation.name (operation.levelParams.map fun _ => .zero)
    let result := mkAppN fn (domain.getAppArgs ++ #[route] ++ sorts ++ #[directory])
    mkLambdaFVars params result

local elab "originalCalendarPacketAcquirerType%" : term => do
  inferType (← originalPacketRouteTerm)

/-- The packet-assembly operation on the installed original routing and directory. -/
noncomputable abbrev SignedCalendarAt.FrozenSuppliedAtRoutes : Type _ := originalCalendarPacketAcquirerType%

/-- At the recorded physical routing, assemble the actual team launches and
the owner, ordered logical calls and placement stored with each one. -/
noncomputable def SignedCalendarAt.frozenSuppliedAtRoutes : SignedCalendarAt.FrozenSuppliedAtRoutes := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← originalPacketRouteTerm)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
