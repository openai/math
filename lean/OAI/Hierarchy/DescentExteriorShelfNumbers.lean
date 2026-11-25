import OAI.Hierarchy.DescentExteriorTableBits
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Packed exterior row count and the common dyadic shelf span -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior
variable (j r t e : ℕ)
def rows := e*2^(j+r)
def exponent := max (Nat.clog 2 (rows j r e)) (tableBits j r t)
def span := 2^(exponent j r t e)

theorem row_room : rows j r e≤ span j r t e :=
  (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_left ..))

end Hierarchy.DescentExteriorShelf

end OAI
