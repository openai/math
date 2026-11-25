import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # Physical input cells of the terminal pointer interpreter -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentOperandStateBanks DescentSharedCableNames
noncomputable section
variable {D cap N A : ℕ}

structure CellInputs (D cap N A : ℕ) where
  n : ℕ
  arity : Fin N→ℕ
  pointer : Fin (N*A)→ Pointer
  chips : Fin (2*cap)→ Option (Stage.Live D cap)

namespace CellInputs
variable (t : CellInputs D cap N A)
def active (i : Fin (N*A)) : Prop :=
  let z:=finProdFinEquiv.symm i
  z.1.val < t.n ∧ z.2.val < t.arity z.1

end CellInputs

def reindex (pin : ℕ→ℕ) : Pointer→ Pointer
  | .privateWord a=>.privateWord a
  | .cable peer serial chunk=>.cable peer serial chunk
  | .pin j chunk=>.pin (pin j) chunk

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
