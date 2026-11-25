import OAI.Hierarchy.DescentRecipeNodeTypes
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentKernelHistory DescentSIMDLookup
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

/-- A dated scalar field is first addressed at its physical rack, group and block (packed)
and then decoded at its actual, possibly noncontiguous, node number. -/
structure Register (B : BitDescription W) where
  field : ℕ
  nodes : ℕ
  packed : NodeOrder.All B→ℕ→Fin 3→Cell (field*nodes)
  number : NodeOrder.All B→Fin nodes

def Register.word {B : BitDescription W} (bank : Register B) (x : NodeOrder.All B) (j : ℕ) (f : Fin 3) : ℕ :=
  ((encode bank.field bank.nodes).symm (bank.packed x j f) (bank.number x)).val

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
