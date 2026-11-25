import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProbeStagePublicGroups

namespace OAI
/-! # The price instruction on the typed physical stock bank -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical
noncomputable section

/-- Physical prices read exactly one actual integer inventory cell, then use the
payload or signed-axis quote ROM parameters. -/
def stockQuotes {z d k w : ℕ} (phase : PhasePrice) (payload signed base : ℕ) (mem : Memory w)
    (i : Commodity (Fin (2^z)) (2*rounds d+1) k) : ℝ :=
  phase.quote (match i with | .inl _ => payload | .inr _ => signed) (PurchaseInventory.stock base mem i)

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
