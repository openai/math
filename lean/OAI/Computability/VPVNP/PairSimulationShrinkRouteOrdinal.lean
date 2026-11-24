import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource

/-!
# The dense ordinal passed as state to a selected shrinking map
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM Compression MapResidentRows
open scoped Fin.CommRing

/-- The dense motif ordinal loaded as the sixth operand of a resident row. -/
noncomputable def rowOrdinalWord {w a g : ℕ} (X : State a (packingLaneBits a g)) (side : Bool)
    (site : Site X) (i : Fin (order X side site).length) : Word w :=
  ((ordinal X (MapResidentRows.entry X side site i).1).val : Word w)

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
