import OAI.Hierarchy.DescentSeedInitialWidths
import OAI.Hierarchy.DescentReentryGroupStage
import OAI.Hierarchy.DescentGroupStage

namespace OAI
/-! # Complete edge-grain receipts at initialization and after a physical reset -/

namespace Hierarchy.DescentSixParty.ResetInput
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)

theorem ordinaryWorld_divides (e : (ordinaryWorld Z T).graph.Edge) :
    Z.unit∣(ordinaryWorld Z T).graph.width e := by
  rcases e with old|⟨parent,j⟩
  · exact reentry_divides Z T old.val
  · exact dvd_rfl

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
