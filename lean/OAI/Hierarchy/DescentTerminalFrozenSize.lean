import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Size of the frozen roster's three literal tables -/
namespace Hierarchy.DescentTerminalFrozenRoster.ROM

def size (f k : ℕ) := 2^f+2^k+2^k*2^f

end Hierarchy.DescentTerminalFrozenRoster.ROM

end OAI
