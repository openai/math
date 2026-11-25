import Mathlib.Data.Nat.Log

namespace OAI
/-! # Height of a padded native control list -/

namespace Hierarchy.Tagged

/-- The stable sort uses the least power of two accommodating its actual rows
and the parent row count. At most a factor of two is spent on this padding. -/
def controlHeight (h rows : ℕ) := Nat.clog 2 (max (2^h) rows)

end Hierarchy.Tagged

end OAI
