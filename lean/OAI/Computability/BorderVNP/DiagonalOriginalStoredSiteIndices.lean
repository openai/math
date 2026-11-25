import OAI.Computability.BorderVNP.DiagonalBeforeIssuedCalls
import OAI.Computability.BorderVNP.DiagonalSparsePlacementEvidence

/-! # Indices of the physical receipt at an original calendar site

The input to the sparse packet issuer fixes its owner table, logical row
order, and source calls. The placement equivalence fixes the directory in
the original geometry. These choices precede the receipt of the native
source and are recovered from the types of those two operations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta RoutingISA.Evaluator CellPacketGeometry
open BorderVNP.Cube.Physical.NativeAssignments.CoreDirectory

/-- Coordinates of the original owner and read evidence together with the
original saved-placement directory at the same field and team. -/
structure OriginalStoredSiteIndices where
  /-- The owner function whose values the native program reads from its owner bank. -/
  owner : Expr
  /-- The type of a received cell row at the selected field and team. -/
  indexType : Expr
  /-- The native logical index associated to each original row. -/
  index : Expr
  /-- The source call expected at each such row. -/
  want : Expr
  /-- Number of tag keys of the original site directory. -/
  tags : Expr
  /-- The original directory bounds its rows by this parameter plus one. -/
  rows : Expr
  /-- The original geometry directory, before moving the saved placement to the emitted directory. -/
  directory : Expr

/-- The literal dependent pair expected by the supplied packet assembler at
the original field and team. Its first projection is the native source. -/
def originalStoredPacketType (issuer f u : Expr) : MetaM Expr := do
  let .forallE _ packets _ _ ← whnf (← inferType issuer) | throwError "missing original packet map"
  let .forallE _ _ column _ ← whnf packets | throwError "missing original packet field"
  let .forallE _ _ site _ ← whnf (column.instantiate1 f) | throwError "missing original packet team"
  let some sigma ← whnfUntil (site.instantiate1 u) ``Sigma | throwError "expected an original native packet"
  return sigma

private def originalDirectoryIndices (placement : Expr) : MetaM (Expr × Expr × Expr) := do
  forallBoundedTelescope (← inferType placement) (some 1) fun logical conclusion => do
    let some movement ← whnfUntil conclusion ``Iff | throwError "missing original placement equivalence"
    let some available ← whnfUntil movement.getAppArgs[0]! ``Nonempty | throwError "missing original placement"
    let some saved ← whnfUntil available.getAppArgs[0]! ``SavedSparsePlacement |
      throwError "missing original saved sparse directory"
    let #[key,_,rows,directory,_] := saved.getAppArgs | throwError "unexpected saved placement arguments"
    let some keys ← whnfUntil key ``Fin | throwError "expected finite original tags"
    let tags := keys.getAppArgs[0]!
    let free := #[tags,rows,directory].foldl collectFVars {}
    if free.fvarSet.contains logical[0]!.fvarId! then throwError "directory depends on a temporary source"
    return (tags,rows,directory)

/-- Read the seven source coordinates from the issuer at `f` and `u` and the
placement equivalence at that original history. The resulting expressions
contain none of the temporary source, receipt or row variables. -/
def originalStoredSiteIndices (issuer f u placement : Expr) : MetaM OriginalStoredSiteIndices := do
  let (tags,rows,directory) ← originalDirectoryIndices placement
  let site ← originalStoredPacketType issuer f u
  withLocalDeclD `native site.getAppArgs[0]! fun native => do
    let some pair ← whnfUntil (mkApp site.getAppArgs[1]! native) ``Prod |
      throwError "expected the original issued receipt and placement"
    let some lift ← whnfUntil pair.getAppArgs[0]! ``PLift | throwError "missing original receipt"
    let some receipt ← whnfUntil lift.getAppArgs[0]! ``IssuedReceipt | throwError "missing original row evidence"
    let constructor := mkAppN (mkConst ``IssuedReceipt.mk receipt.getAppFn.constLevels!) receipt.getAppArgs
    forallBoundedTelescope (← inferType constructor) (some 2) fun observations _ => do
      let some table ← whnfUntil (← inferType observations[0]!) ``RoutingISA.CellDispatch.OwnerTable |
        throwError "missing the original owner table"
      let owner := table.getAppArgs.back!
      forallBoundedTelescope (← inferType observations[1]!) (some 1) fun row equality => do
        let some read ← whnfUntil equality ``Eq | throwError "missing the logical read at the original row"
        let lhs := read.getAppArgs[1]!
        unless lhs.isApp do throwError "missing the native logical index"
        let indexType ← inferType row[0]!
        let index ← mkLambdaFVars row lhs.appArg!
        let want ← mkLambdaFVars row read.getAppArgs[2]!
        -- The original calendar has shared expressions. Traverse each one only once.
        let free := #[owner,indexType,index,want].foldl collectFVars {}
        for temporary in (observations.push native) ++ row do
          if free.fvarSet.contains temporary.fvarId! then throwError "source read depends on a temporary witness"
        return ⟨owner,indexType,index,want,tags,rows,directory⟩

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
