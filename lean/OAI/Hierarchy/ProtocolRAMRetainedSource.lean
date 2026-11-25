import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # The nonzero paid originals and the fixed goods and reserve rows -/

namespace Hierarchy.ProtocolRAMLiveTurnOrder
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard WireTelescope
variable {h W k edges : ℕ} (fixed : Fin edges → ℕ)
local notation "Sources" => SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
  (Columns h (2^W) × Fin k)

def retain : Sources → Prop
  | .inl e => 0 < fixed e
  | .inr _ => True

end Hierarchy.ProtocolRAMLiveTurnOrder

end OAI
