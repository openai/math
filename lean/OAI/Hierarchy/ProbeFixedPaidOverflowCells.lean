import OAI.Hierarchy.ProbeFixedPaidFeedCells
import OAI.Hierarchy.ProbeFixedPaidSlabCell
import OAI.Hierarchy.ProbeFixedReadbackRun
import OAI.Hierarchy.ProbeFixedReplayPurchase
import OAI.Hierarchy.ProbeFixedOuterFeed
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # Checked paid overflow cells on the actual source calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit

theorem paid_feed_cell (π : Equiv.Perm (Fin (2^z))) (mem fixture : Memory W)
    (run : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)
    (b : Boundary) (live : Event.feed b∈events v.mesh) (c : CommodityColumn)
    (column : c∈(lay b).columns) (i : Fin c.rows) :
    ((checkedOut C ((G).endAddress v.mesh) mem) (c.overflow+i.val)).val≤(v.keepLimit+1)*width :=
  v.paid_feed_cell_of_stock P z width r banks src tab dst owners mem
    ⟨run.nativeStock,run.steps,run.digitBudget,run.payload,run.dimension,run.endFits,run.slices⟩
    b live c column i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
