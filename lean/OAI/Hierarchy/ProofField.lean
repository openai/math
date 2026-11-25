import Lean

namespace OAI
namespace Hierarchy

open Lean Meta Elab Term

/-- Project fields pointwise under a proof producer's original telescope. -/
scoped elab "proofField% " producer:ident " [" fields:ident,* "]" : term => do
  let source ← getConstInfo (← resolveGlobalConstNoOverload producer)
  forallTelescope source.type fun inputs _ => do
    let mut result := mkAppN (Lean.mkConst source.name (source.levelParams.map Level.param)) inputs
    for field in fields.getElems do
      let name ← resolveGlobalConstNoOverload field
      let some info := (← getEnv).getProjectionFnInfo? name
        | throwErrorAt field "expected a structure projection"
      result := .proj info.ctorName.getPrefix info.i result
    mkLambdaFVars inputs result

end Hierarchy
end OAI
