import Lean

/-! # Recovering a native operation from its returned data

Both a retained reporter and its earlier writer store the indices needed by their
joint operations. Recovering the argument positions on the general declaration
first avoids searching for those indices in a complete calibrated circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.RecordedApplication

open Lean Meta

private def throughBinder (type : Expr) (last : Name) (count : Nat := 0) : MetaM Nat := do
  match type with
  | .forallE name _ body _ =>
    if name == last then return count + 1
    throughBinder body last (count + 1)
  | _ => throwError "the native declaration has no initial segment ending in {last}"

private def findBinder (parameters : Array Expr) (label : Name) : MetaM Expr := do
  for parameter in parameters do
    if (← parameter.fvarId!.getUserName) == label then return parameter
  throwError "the native declaration has no {label} argument in the requested segment"

/-- Read the arguments through the named binder of `operation` from the pre-existing
typed `evidence`. The same `coordinates` projection is applied to the declaration's
general parameters and to the particular physical receipts. A missing general
parameter fails elaboration before any application is constructed. -/
def fromEvidence (operation last : Name) (evidence : Array (Name × Expr))
    (coordinates : Array Expr → MetaM (Array Expr × List Level)) : MetaM Expr := do
  let info ← getConstInfo operation
  let count ← throughBinder info.type last
  let positions ← forallBoundedTelescope info.type (some count) fun parameters _ => do
    let general ← evidence.mapM fun (label, _) => findBinder parameters label
    let (available, _) ← coordinates general
    parameters.mapM fun parameter => do
      let some position := available.idxOf? parameter
        | throwError "the receipts do not determine the native argument {← parameter.fvarId!.getUserName}"
      return position
  let (observed, levels) ← coordinates (evidence.map Prod.snd)
  unless levels.length == info.levelParams.length do
    throwError "the native declaration and its receipt have different universe parameters"
  let arguments ← positions.mapM fun i => do
    let some value := observed[i]? | throwError "the returned receipt has too few coordinates"
    return value
  return mkAppN (mkConst operation levels) arguments

end Diagonal.RecordedApplication

end BorderVNP
end Computability
end OAI
