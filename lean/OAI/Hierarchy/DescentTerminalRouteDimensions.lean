import Mathlib.Data.Nat.Log

namespace OAI
/-! # Widths of the actual terminal book tokens and route-ledger lookup -/
namespace Hierarchy.DescentTerminalLocalPortBook
def nameBits (G M : ℕ) := Nat.clog 2 (G*M+1)
end Hierarchy.DescentTerminalLocalPortBook

namespace Hierarchy.DescentTerminalRouteRows
def rowBits (q a : ℕ) := 2*(q*(a+1))
end Hierarchy.DescentTerminalRouteRows

namespace Hierarchy.DescentTerminalRouteLedger
def radix (W c : ℕ) := W*(2^c*2^(W*c))
end Hierarchy.DescentTerminalRouteLedger

end OAI
