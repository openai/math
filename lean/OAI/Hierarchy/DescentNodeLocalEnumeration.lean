import OAI.Hierarchy.DescentRecipeNodeTypes

namespace OAI
/-! # Enumerating the original vertices of a local recipe -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
abbrev Local (B : BitDescription W) := ∀v,(B.recipe v).Node ≃ Fin (Fintype.card (B.recipe v).Node)

end Hierarchy.DescentLocalArchiveOrder

end OAI
