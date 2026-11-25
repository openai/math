import OAI.Hierarchy.ProtocolRAMCalendarStripArena
import OAI.Hierarchy.ProtocolRAMPurchaseDensity
import OAI.Hierarchy.ProtocolRAMThresholdExponent

namespace OAI
/-! # Native signed threshold reads from capped physical stock -/

namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT
noncomputable section

def forCap (headerEnd cap : ℕ) : Slab := ⟨headerEnd,ProtocolRAMPurchaseSampler.bits cap⟩

variable {z d k q depth digits ports : ℕ}

theorem localized_table (u : Slab) (s : StripChart.Boards z d k q depth)
    (b : StripDirectory.Boards z d k q digits ports) (base : ℕ) :
    ((u.localize s b base).market.shelf.table).size=2^(z+u.thresholdExtra) := rfl

/-- Stock is read at its actual per-tile, stage, and sign address. All of these
addresses may be populated from either a clipped store or an earlier debit. -/
theorem threshold_reads (s : StripChart.Boards z d k q depth) (b : StripDirectory.Boards z d k q digits ports)
    (headerEnd cap payload base : ℕ) (mem : Shelf.Mem z d) (width : payload≤2^z)
    (stock : ∀c : Commodity (Fin (2^z)) (2*rounds d+1) k,PurchaseInventory.stock b.market.shelf.stockBase mem c≤ cap*payload) :
    let u:=forCap headerEnd cap
    let sh:=(u.localize s b base).market.shelf
    ∀v : Tile z d, ∀a : Fin k×Bool,stockBits sh.stockBase k mem v a < sh.table.size :=
  fun v a=>ProtocolRAMPurchaseSampler.threshold_index (stock (.inr ((v.2,stageNumber v.1),a))) width

theorem threshold_reads_clipped (s : StripChart.Boards z d k q depth) (b : StripDirectory.Boards z d k q digits ports)
    (headerEnd cap payload base : ℕ) (mem : Shelf.Mem z d) (width : payload≤2^z)
    (raw : Commodity (Fin (2^z)) (2*rounds d+1) k→ℕ)
    (store : ∀c,PurchaseInventory.stock b.market.shelf.stockBase mem c=min (raw c) (cap*payload)) :
    let u:=forCap headerEnd cap
    let sh:=(u.localize s b base).market.shelf
    ∀v : Tile z d, ∀a : Fin k×Bool,stockBits sh.stockBase k mem v a < sh.table.size :=
  threshold_reads s b headerEnd cap payload base mem width (fun c=>(store c).le.trans (Nat.min_le_right ..))

end
end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end OAI
