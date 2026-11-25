import OAI.Computability.BorderVNP.DiagonalFundedCableRows
import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys

/-! # Placements and writers at equal finite cable rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing

/-- Reindexing the numbered cables along their size equality preserves both
complete native placement functions. -/
theorem placements_beforeCableCast {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) {cables : ℕ} (same : ne = cables) (atCable : N.Edge ↪ Fin cables)
    (retained : HEq atCable edge) :
    privatePair N cell atCable port dir old live gap = privatePair N cell edge port dir old live gap ∧
    livePair N cell atCable port dir old live gap = livePair N cell edge port dir old live gap := by
  subst cables
  cases eq_of_heq retained
  exact ⟨rfl,rfl⟩

end Packing.RoutingOutputs.NativeDemands

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM
/-- The same physical writer on two equal private/live placement functions. -/
def SlottedWriter.atEqualPlacements {w : ℕ} {ar : CubeArena.Layout} {D : Packing.Directory.Layout}
    {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {pub : Arg → Word w} {mem : Memory w}
    {base : ℕ} {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (writer : SlottedWriter ar D pp lp pins pub mem base cell id width)
    (pp' lp' : ℕ → ℕ × ℕ) (same : pp=pp' ∧ lp=lp') :
    SlottedWriter ar D pp' lp' pins pub mem base cell id width := by
  rcases same with ⟨rfl,rfl⟩
  exact writer

end RoutingISA.Evaluator

namespace Diagonal
open Lean Meta RoutingISA.Evaluator ExternalSew.Fragments Packing.RoutingOutputs

private def nativeWriterType (type : Expr) : MetaM Expr := do
  let some writer ← whnfUntil type ``SlottedWriter | throwError "expected a native slotted writer"
  return writer

private def nativeArgument (app : Expr) (key : Name) : MetaM Expr := do
  let mut t := (← getConstInfo app.getAppFn.constName!).type
  for v in app.getAppArgs do
    if t.bindingName! == key then return v
    t := t.bindingBody!
  throwError "missing native argument {key}"

/-- Recover equality of the two physical placement functions from the original
observed cable count and the returned writer's literal edge-index cast. -/
def fundedPlacementFunctionEquality (observed donorType requiredType : Expr) : MetaM Expr := do
  let actual ← nativeWriterType donorType
  let wanted ← nativeWriterType requiredType
  let some src ← whnfUntil (← nativeArgument actual `pp) ``NativeDemands.privatePair | throwError "expected returned placements"
  let some dst ← whnfUntil (← nativeArgument wanted `pp) ``NativeDemands.privatePair | throwError "expected funded placements"
  let some came ← whnfUntil (← inferType observed) ``CableRows | throwError "expected the recorded cable rows"
  let some edged ← whnfUntil (← nativeArgument came `edgeID) ``Function.Embedding.trans | throwError "expected the calibrated cable renumbering"
  let some adjusted ← whnfUntil edged.getAppArgs.back! ``Equiv.toEmbedding | throwError "missing the calibrated finite equivalence"
  let some he ← whnfUntil adjusted.getAppArgs.back! ``finCongr | throwError "missing the observed cable count equality"
  let edge ← nativeArgument src `edgeID
  let some castEdge ← whnfUntil edge ``cast | throwError "expected the returned edge cast"
  let aligned := mkAppN (mkConst ``cast_heq castEdge.getAppFn.constLevels!) castEdge.getAppArgs
  return mkAppN (← mkConstWithLevelParams ``NativeDemands.placements_beforeCableCast)
    (dst.getAppArgs ++ #[← nativeArgument src `ne,he.getAppArgs.back!,edge,aligned])

/-- Move an actual returned writer to the original funded edge rectangle using
the same observed cable rows and the funded reader's SlottedWriter domain. -/
def fundedNativeWriterAt (observed donor requiredType : Expr) : MetaM Expr := do
  let input ← inferType donor
  let src ← nativeWriterType input
  let dst ← nativeWriterType requiredType
  let same ← fundedPlacementFunctionEquality observed input requiredType
  return mkAppN (mkConst ``SlottedWriter.atEqualPlacements src.getAppFn.constLevels!)
    (src.getAppArgs ++ #[donor,← nativeArgument dst `pp,← nativeArgument dst `lp,same])

end Diagonal

end BorderVNP
end Computability
end OAI
