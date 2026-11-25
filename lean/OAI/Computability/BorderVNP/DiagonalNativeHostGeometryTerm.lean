import OAI.Computability.BorderVNP.PackedCellAddressCircuit
import Lean

/-! # Applying a returned writer to its recorded circuit geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Apply the writer's geometry continuation with the widths and alphabet stored in its
field rectangle. The remaining operands include the placement and capacity of that writer. -/
elab (name := exactHostGeometry) "exactHostGeometry%" install:ident "fields" rectangle:term:max
    "arguments" "[" operands:term,* "]" : term => do
  let continuation ← elabTerm (← `(@$install)) none
  let fields ← elabTerm rectangle none
  let some shape ← whnfUntil (← inferType fields) ``Packing.CellAddressCircuit.Fields
    | throwError "expected the writer's circuit field rectangle"
  let indices := shape.getAppArgs
  unless indices.size == 8 do throwError "expected eight circuit field indices"
  let alphabet := indices[7]!
  let finite ← synthInstance (← mkAppM ``Fintype #[alphabet])
  let geometry := mkAppN continuation #[indices[4]!, indices[5]!, indices[6]!, alphabet, finite, fields]
  return mkAppN geometry (← operands.getElems.mapM fun term => elabTerm term none)

end Diagonal

end BorderVNP
end Computability
end OAI
