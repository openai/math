import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport
import OAI.Computability.BorderVNP.DiagonalOriginalStoredReportShape
import OAI.Computability.BorderVNP.DiagonalOriginalStoredSiteIndices

/-! # The sparse call packet carried by a stored original report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta RoutingISA.FragmentRows
open BorderVNP.Cube.Physical.NativeAssignments.CoreDirectory

/-- Construct the packet at its original field and team. The native launch, owner table,
source reads and saved placement all come from the same certified report. -/
def originalStoredPacketValue (issuer placementAtHistory f u storedAt : Expr) : MetaM Expr := do
  let certified ← storedReportAtOriginalSite storedAt
  let report := mkProj ``Subtype 0 certified
  let some launchField := (getStructureFields (← getEnv) ``EmittedReport).findIdx? (· == `launch) |
    throwError "missing the sparse launch on the original report"
  let launch := mkProj ``EmittedReport launchField report
  let native := mkProj ``SparseEmission.NativeInputAt 0 launch

  -- In FundedFacts, the ten equalities through the native identity precede
  -- the owner-table observation, the ordered logical reads and the saved placement.
  let mut physical := mkProj ``Subtype 1 certified
  for _ in [:10] do physical := mkProj ``And 1 physical
  let owner := mkProj ``And 0 physical
  let tail := mkProj ``And 1 physical
  let reads := mkProj ``And 0 tail
  let saved := mkProj ``And 1 tail

  let site ← originalStoredPacketType issuer f u
  let some pair ← whnfUntil (mkApp site.getAppArgs[1]! native) ``Prod |
    throwError "expected a receipt and placement for this sparse source"
  let some lifted ← whnfUntil pair.getAppArgs[0]! ``PLift | throwError "missing the original receipt"
  let some receipt ← whnfUntil lifted.getAppArgs[0]! ``IssuedReceipt |
    throwError "expected the owner and ordered logical reads of the issued call"
  let observed := mkAppN (mkConst ``IssuedReceipt.mk receipt.getAppFn.constLevels!)
    (receipt.getAppArgs ++ #[owner, reads])
  let evidence := mkAppN (mkConst ``PLift.up lifted.getAppFn.constLevels!) (lifted.getAppArgs.push observed)

  let transport := mkApp placementAtHistory receipt.getAppArgs.back!
  let some movement ← whnfUntil (← inferType transport) ``Iff |
    throwError "expected the original-to-emitted placement equivalence"
  let moved := mkAppN (mkConst ``Iff.mp) (movement.getAppArgs ++ #[transport, saved])
  let some available ← whnfUntil movement.getAppArgs[1]! ``Nonempty |
    throwError "missing the saved placement in the emitted directory"
  let placed := mkApp2 (mkConst ``Classical.choice available.getAppFn.constLevels!) pair.getAppArgs[1]! moved
  let details := mkAppN (mkConst ``Prod.mk pair.getAppFn.constLevels!) (pair.getAppArgs ++ #[evidence, placed])
  return mkAppN (mkConst ``Sigma.mk site.getAppFn.constLevels!) (site.getAppArgs ++ #[native, details])

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
