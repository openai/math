import Mathlib.Data.Fin.Basic

namespace OAI
/-! # The closed physical port table, with one final stay port -/
namespace Hierarchy.DescentResetOriginHaloRAM
variable {H D : ℕ}

def closed (p : Fin H→Fin D→Option (Fin H)) (v : Fin H) : Fin (D+1)→Option (Fin H) :=
  Fin.lastCases (some v) (p v)

end Hierarchy.DescentResetOriginHaloRAM

end OAI
