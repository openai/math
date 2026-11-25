import OAI.Computability.BorderVNP.DiagonalCalendarObservedWriterOnOriginal
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredResidentOwner
import OAI.Computability.BorderVNP.DiagonalOriginalWriterResidentWords

/-! # The resident report's writer on its original calendar field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta TeamContraction
open private argument atHead argumentsOf applyNamed from OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership

set_option maxRecDepth 16000
set_option maxHeartbeats 3200000

/-- Use the original selector, field and scan from the already observed writer.
The resident coordinates are taken at that field's own history. -/
private def residentWriterTerm : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.OriginalWriterAtFrameEntries
    | throwError "expected the original writer on the actual calendar entries"
  forallTelescope shape.value fun args _ => do
    let some values ← args.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == `values)
      | throwError "expected the calendar's input matrices"
    let field := args.back!
    let hist := mkProj ``Sigma 0 (mkProj ``Sigma 1 field)
    let coordinates := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenRegisteredResidentCoordinates)
      ((args.extract 0 (values+1)).push hist)
    let owners := mkProj ``And 0 coordinates
    let labels := mkProj ``And 1 coordinates
    let ownerEq ← atHead (← inferType owners) ``Eq
    let labelEq ← atHead (← inferType labels) ``Eq
    let physical := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenObservedWriterOnOriginal) args
    let observed ← atHead (← inferType (mkProj ``And 0 physical)) ``PreparationFrame.OwnedRouteOn
    let nativeArgs ← argumentsOf observed
    let scanEq ← atHead (← inferType (mkProj ``And 1 physical)) ``Eq
    let fixed ← applyNamed ``PreparationFrame.originalWriterAndWords
      (#[ (`teams,← argument nativeArgs `t), (`registered,ownerEq.getAppArgs[1]!), (`resident,ownerEq.getAppArgs[2]!),
          (`packetLabel,labelEq.getAppArgs[1]!), (`residentLabel,labelEq.getAppArgs[2]!),
          (`scan,scanEq.getAppArgs[2]!), (`after,scanEq.getAppArgs[1]!),
          (`physical,physical), (`names,owners), (`labels,labels) ] ++ nativeArgs)
    mkLambdaFVars args fixed

local elab "residentOriginalWriter%" : term => do inferType (← residentWriterTerm)

/-- The original registered field retained at the native report's owner coordinates. -/
abbrev SignedCalendarAt.NativeOriginalWriterStatement : Prop := residentOriginalWriter%

/-- Recover the full native transmission and physical owner scan while preserving
the registered selector, its complete payload and all its owner words. -/
theorem SignedCalendarAt.frozenNativeWriterOnOriginal : SignedCalendarAt.NativeOriginalWriterStatement := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← residentWriterTerm)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
