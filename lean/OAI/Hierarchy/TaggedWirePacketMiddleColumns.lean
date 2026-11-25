import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Public column enumeration for a signed party's intermediate role slab -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
abbrev MiddleField (n : ℕ) := (Fin n×Fin 6)⊕((Fin n×Bool)×(Fin n×Bool))
def middleColumns (n : ℕ) := Fintype.card (MiddleField n)
def middleNumber (n : ℕ) : MiddleField n≃Fin (middleColumns n) := Fintype.equivFin _
end Hierarchy.WireTelescope.PacketTurns
end

end OAI
