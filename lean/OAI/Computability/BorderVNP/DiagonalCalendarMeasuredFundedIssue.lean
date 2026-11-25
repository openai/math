import OAI.Computability.BorderVNP.DiagonalCalendarMeasuredOwnedColumn
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacementData

/-! # Issued private rows on the calendar's measured funded packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta

/-- Recover the value used by an installed projection, including a lifted closed proof. -/
private partial def receiverOf (structureName : Name) (index : Nat) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .proj n i value := e then
    if n == structureName && i == index then return value
  let .const n levels := e.getAppFn | throwError "expected the installed {structureName} projection"
  let info ← getConstInfo n
  let some value := info.value? (allowOpaque := true) | throwError "cannot read the installed projection {n}"
  receiverOf structureName index ((value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs)

/-- Use the acquisition and the continuation carried by the calendar's installed owner table. -/
private def measuredIssuedColumn : MetaM Expr := do
  let ownedName := ``SignedCalendarAt.measuredOwnedColumn
  let .defnInfo owned ← getConstInfo ownedName
    | throwError "expected the measured calendar owner column"
  lambdaTelescope owned.value fun xs body => do
    let owner ← receiverOf ``Subtype 1 body.getAppArgs.back!
    unless owner.getAppFn.isConstOf ``SignedCalendarAt.frozenBaseOwnerOfFundedCandidates do
      throwError "expected the owner returned by the funded calendar"
    let ownerArgs := owner.getAppArgs
    let calls := ownerArgs.back!
    let .proj ``Prod 1 packet := calls.getAppArgs.back!
      | throwError "expected the native calls on the installed sparse source"
    let fields := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenIssuedReadbackOfCandidates)
      (ownerArgs.extract 0 (ownerArgs.size-2))
    let measured := mkAppN (← mkConstWithLevelParams ownedName) xs
    let outstanding ← whnf (← inferType measured)
    let issued ← whnf outstanding.bindingDomain!
    withLocalDecl `f issued.binderInfo issued.bindingDomain! fun f => do
      let retained := mkAppN fields #[mkProj ``Prod 0 packet,calls,f]
      let rows ← mkLambdaFVars #[f] (mkProj ``Prod 0 retained)
      mkLambdaFVars xs (mkApp measured rows)

local elab "measuredIssuedColumnType%" : term => do inferType (← measuredIssuedColumn)

/-- The guarded return required after the measured calendar has acquired and issued each private row. -/
noncomputable abbrev SignedCalendarAt.MeasuredFundedIssuedResult : Type _ := measuredIssuedColumnType%

/-- Continue the calendar column with the private rows issued on the same packet and continuation
whose owner table was installed. The remaining input is the original guarded execution. -/
noncomputable def SignedCalendarAt.measuredFundedIssuedColumn :
    SignedCalendarAt.MeasuredFundedIssuedResult := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← measuredIssuedColumn)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
