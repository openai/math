import OAI.Computability.BorderVNP.PackedCellAddressPhysical

/-! # Parameters of the representation returned by the signed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressPhysical

open Lean Meta Elab Term

/-- Read a named parameter of the actual address representation, retaining the
cable embedding at the writer's physical width and the same field assignment. -/
elab "issuedNetworkField%" proof:term:max key:ident : term => do
  let represented ← elabTerm proof none
  let some ty ← whnfUntil (← inferType represented) ``Represents
    | throwErrorAt proof "expected a proof that the writer fields represent the network"
  let declaration ← getConstInfo ``Represents
  forallTelescope declaration.type fun parameters _ => do
    for parameter in parameters, value in ty.getAppArgs do
      if (← parameter.fvarId!.getUserName) == key.getId.eraseMacroScopes then
        return value
    throwErrorAt key "unknown parameter of the address representation"

end Packing.CellAddressPhysical

end BorderVNP
end Computability
end OAI
