import OAI.Hierarchy.ProbeFixedMarketLayout
import OAI.Hierarchy.ProtocolRAMBootHigh

namespace OAI
/-! # Original market pages of the fixed charged bootstrap -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart PurchaseFrozen
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "A" => v.privateArena P z width
local notation "d" => (2^v.W)

abbrev catalystMarkets := Whole.markets v.mesh v.finish (v.basePhase width) (v.nativeFormats P z width)

theorem catalyst_market_low (i : Fin (Whole.attempts v.mesh).length) :
    (A).first≤Boot.low (v.catalystMarkets P z width i) := by
  let a:=(Whole.attempts v.mesh)[i.val]
  let sizes := v.sized (v.seed P z width) width
  let base := (A).base v.mesh (.attempt a)
  change (A).first ≤ ((v.nativeFormats P z width a).atTime v.mesh v.finish (v.basePhase width) a).shelf.thresholdBase
  rw [(v.market_shelf_fields P z width a).1]
  exact (Nat.le_add_right (A).first _).trans
    ((Nat.le_add_right base (Slab.selectorSpan sizes)).trans (Nat.le_add_right _ (Slab.failureSpan sizes)))

theorem catalyst_market_layout (heap : heapEnd z d copies≤P.joint.initial) :
    Boot.Layout (v.catalystMarkets P z width) ((A).endAddress v.mesh) :=
  v.market_layout P z width heap

theorem catalyst_market_layout_at (size : ℕ) (heap : heapEnd z d copies≤P.joint.initial)
    (room : (A).endAddress v.mesh ≤ size) : Boot.Layout (v.catalystMarkets P z width) size :=
  (v.market_layout P z width heap).extend room

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
