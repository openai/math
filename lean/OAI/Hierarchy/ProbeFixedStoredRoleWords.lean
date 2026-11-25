import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProbeStripDirectory

namespace OAI
/-! # The stored inventory operands for a payload or a purchased ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage ProbeStage.CoreBoard AdaptiveProbe StripDirectory
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
local notation "B" => v.nativeBoards P h width

/-- The two stored-role sources use the very slots debited by the native bank. -/
def widePayloadStored (_P : v.Placement) (h _width _phase _trial : ℕ) : PayloadStrip.Quotes (Stages h (2^v.W)) k→Expr :=
  payloadSlot h

def widePurchaseStored (phase trial _slice _inner : ℕ) : ChainStrip.Axes v.depth k→Expr :=
  let sh:=((B).outer phase trial).market.shelf
  allChainSlot (z:=h) (d:=2^v.W) sh v.sampler v.depth
    (stratumHeader h (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader phase trial))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
