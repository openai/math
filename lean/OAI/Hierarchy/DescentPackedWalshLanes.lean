
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Lane exponent of the packed Walsh transform -/
namespace Hierarchy.DescentPackedWalsh
def laneBits (m h b : ℕ) := min m (Nat.log 2 (h/(8*b)))

end Hierarchy.DescentPackedWalsh

end OAI
