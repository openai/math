import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # A finite public interval of RAM words -/
namespace Hierarchy.DescentPackedColony.Phase.Arena
open Computability.VPVNP.BurstRAM PrivateRAM
variable {w : ℕ}
/-- A single annulus of actual word addresses; all table entries are computed
from the public parameters alone and all previous dynamic operands are lower. -/
structure Image (w : ℕ) where
  low : ℕ
  stop : ℕ
  value : ℕ→Word w

def Image.Resident (s : Image w) (m : Memory w) := ∀u,s.low≤u→u<s.stop→m u=s.value u

end Hierarchy.DescentPackedColony.Phase.Arena

end OAI
