import Mathlib.Data.Nat.Notation

namespace OAI
/-! # Numeric invoice factors for placed blocks and packet lanes -/
namespace Hierarchy.DescentPlacedInvoiceVolume
def volumeFactor (N X : ℕ) :=5+3*N+X+N*X
end Hierarchy.DescentPlacedInvoiceVolume

namespace Hierarchy.DescentPacketPullInvoiceVolume
open DescentPlacedInvoiceVolume
def factor (fields blocks : ℕ) := 4096 * volumeFactor 1 blocks + 1000 * (fields + 1) + 2000
end Hierarchy.DescentPacketPullInvoiceVolume

end OAI
