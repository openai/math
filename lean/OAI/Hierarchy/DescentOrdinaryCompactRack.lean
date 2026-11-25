import Mathlib.Data.Fin.Basic

namespace OAI
/-! The physical prior rack of a compact successor host. -/
namespace Hierarchy.DescentOrdinaryCompactPeer.ROM
variable {H : ℕ}

def rack (N pitch : ℕ) (h : Fin H) : Option (Fin N) :=
  if yes : 0<pitch ∧ h.val/pitch<N then some ⟨h.val/pitch,yes.2⟩ else none

end Hierarchy.DescentOrdinaryCompactPeer.ROM

end OAI
