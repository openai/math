import OAI.Computability.BorderVNP.DiagonalReportArgumentEmission

/-! # Supplying the emission read on a returned calendar report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Bind every state retained at the original scan, then apply the reached emitter
to the original twenty report inputs and the six inputs of its sparse return. -/
private def provideReturnedReport (required provider : Expr) : MetaM Expr := do
  let inputs := #[`operands, `histories, `delivery, `table, `records, `writer, `states, `substitution,
    `words, `route, `result, `handoff, `observed, `guard, `u, `same, `advance, `run, `seed, `alloc]
  let tailInputs := #[`emission, `firstRun, `firstBank, `firstMem]
  forallTelescopeReducing required fun retained _ => do
    let requested := inputs ++ tailInputs
    let mut locals : NameMap Expr := {}
    for x in retained do
      let name := (← x.fvarId!.getDecl).userName.eraseMacroScopes
      if requested.contains name then
        if locals.contains name then throwError "ambiguous returned report input {name}"
        locals := locals.insert name x
    let fetch (n : Name) : MetaM Expr := do
      let some x := locals.find? n | throwError "missing returned report input {n}"
      return x
    let prefixArgs ← inputs.mapM fetch
    let tailArgs ← tailInputs.mapM fetch
    let some sparse ← whnfUntil (← inferType tailArgs[0]!) ``RoutingISA.FragmentRows.SparseEmission |
      throwError "expected the original sparse emission"
    let indices := sparse.getAppArgs
    let fit := indices[indices.size-2]!
    let cells := indices.back!
    mkLambdaFVars retained (mkAppN provider (prefixArgs ++ #[fit, cells] ++ tailArgs))

/-- Complete a prepared report argument with the emitter already selected through
delivery. Its original sparse emission determines the fragment fit and cell count. -/
elab "finishOriginalReportArguments% " prepared:term:max " with " provider:term:max : term => do
  let prepared ← elabTerm prepared none
  let provider ← elabTerm provider none
  let completed ← provideReturnedReport (mkProj ``PSigma 0 prepared) provider
  return mkApp (mkProj ``PSigma 1 prepared) completed

end Diagonal

end BorderVNP
end Computability
end OAI
