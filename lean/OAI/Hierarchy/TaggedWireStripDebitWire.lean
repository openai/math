import OAI.Hierarchy.ProtocolRAMPortPaddingCore
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Fixed numerical ports of the original elected repair -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

/-- The original role ordinal names its actual wire. All trailing slots
receive the single prescribed padding value. -/
def stripDebitWire {R α : Type*} [Fintype R] {D : ℕ} (pad : α) (r : R→α) : Fin D→α :=
  PortPadding.extend (fun i=>r ((Fintype.equivFin R).symm i)) pad

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
