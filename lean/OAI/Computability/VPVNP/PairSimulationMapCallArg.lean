import OAI.Computability.VPVNP.PairSimulationMapLookup

/-!
# Word fields of the private motif-call descriptor

Every map initializer reads a fixed set of addresses and widths. Its callers
use this same field order to compile their descriptor writes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapCallSetup

open MapLookup

/-- A fixed descriptor with no derived ends, offsets, or per-copy selector sequence. -/
inductive Arg (D E : Type) where
  | base (f : LabelField D E)
  | demand (e : D)
  | payload (e : E)
  | copies | directory | source | target | hist
  deriving DecidableEq, Fintype

end PairSimulation.MapCallSetup

end VPVNP
end Computability
end OAI
