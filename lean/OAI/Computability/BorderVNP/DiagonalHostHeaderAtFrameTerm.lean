import OAI.Computability.BorderVNP.PackedRoutingHeaders

/-! # Using the startup frame address in a returned routing header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Packing.RoutingOutputs
open Lean Meta Elab Term

/-- Register zero contains the startup frame address. A header read using that register
therefore describes the same routing words at the startup frame. -/
theorem hostHeaderAtFrame {readFrame startup origin cables cells entries : ℕ} {memory : ℕ → ℕ}
    (address : readFrame = startup)
    (header : Header readFrame origin cables cells entries memory) :
    Header startup origin cables cells entries memory := by
  cases address
  exact header

private def startupHeader (address header : Expr) : TermElabM Expr := do
  let some equality ← whnfUntil (← inferType address) ``Eq |
    throwError "expected the returned register's frame equality"
  let some record ← whnfUntil (← inferType header) ``Header |
    throwError "expected the observed routing header"
  let fields := record.getAppArgs
  let args := #[fields[0]!, equality.getAppArgs[2]!] ++ fields.extract 1 fields.size
  return mkAppN (mkConst ``hostHeaderAtFrame) (args ++ #[address, header])

/-- Reindex just the observed header by the numerical frame value in its processor. -/
elab (name := headerAtHostFrame) "headerAtHostFrame% " address:term:max source:term:max : term => do
  startupHeader (← elabTerm address none) (← elabTerm source none)

/-- Return the original private-layout bound and the header at the startup frame from the
pointwise publication at the same exterior and team. -/
elab (name := hostSetupAtFrame) "hostSetupAtFrame% " address:term:max publication:term:max : term => do
  let current ← elabTerm publication none
  let fit := mkProj ``And 0 current
  let header ← startupHeader (← elabTerm address none) (mkProj ``And 0 (mkProj ``And 1 current))
  return mkAppN (mkConst ``And.intro) #[← inferType fit, ← inferType header, fit, header]

end Diagonal

end BorderVNP
end Computability
end OAI
