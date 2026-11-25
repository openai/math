import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs

/-! # Specializing the frozen calendar on a returned route check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta

/-- Specialize a calendar operation to the measurements in the given physical
route checker. The first tuple passed to `build` holds the operative inputs
through the selected pin. The second holds the source operands from its
`FrozenRouteChecks` result, followed by the checker for every pin, history and
subtotal. All components are taken from this one checked declaration. -/
def withCheckedRouteOperands (checker : Name)
    (build : Array Expr → Array Expr → MetaM Expr) : MetaM Expr := do
  let check ← getConstInfo checker
  forallTelescope check.type fun inputs result => do
    let some route ← whnfUntil result ``FrozenRouteChecks
      | throwError "expected the physical calendar route check"
    let actual := route.getAppArgs
    unless inputs.size ≥ 3 && actual.size ≥ 3 do
      throwError "expected the checked pin, history, and subtotal"
    let operative := inputs.extract 0 (inputs.size - 3)
    let checks := mkAppN (← mkConstWithLevelParams checker) operative
    let calibrated := (actual.extract 0 (actual.size - 3)).push checks
    mkLambdaFVars operative (← build operative calibrated)

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
