import Mathlib.Data.Nat.Notation

namespace OAI
/-! # Number of source words in one rotor window -/
namespace Hierarchy.DescentRotorWindowArchive
def count (D L cap : ℕ) := L+D*L+L*(2*cap)+(L*L+D*(D*6))
end Hierarchy.DescentRotorWindowArchive

end OAI
