import Mathlib.Data.Nat.Basic

namespace OAI
namespace Hierarchy.DescentExterior
def keyBits (j r : ℕ) := (j+(j+r))*(j+(j+r))+(j+r)
end Hierarchy.DescentExterior

namespace Hierarchy.DescentExteriorShelf
open DescentExterior
variable (j r t : ℕ)
def tableBits := keyBits j r+2^j*t
end Hierarchy.DescentExteriorShelf

end OAI
