import OAI.Hierarchy.ProtocolRAMCalendarThresholdFit
import OAI.Hierarchy.ProtocolRAMCalendarStockTrials

namespace OAI
/-! # Sign-table addresses in the genuinely stamped trial memory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe PurchaseFrozen PurchaseCT
open ThreeFlat.RAM
noncomputable section
variable {z d k q depth digits ports goods : ℕ}

/-- This form accepts the final placed market, after its failure descriptor
and stock base have been installed from the selected strip format. -/
theorem Market.frozen_threshold (v : Market z d k) (cap payload : ℕ) (C : Chart (wordBits z d copies) q goods)
    (a : Attempt) (m : Shelf.Mem z d) (width : payload≤2^z)
    (span : v.shelf.tableBits=z+ProtocolRAMPurchaseSampler.bits cap)
    (bounded : StockBound.Bounded z (2*rounds d+1) k v.shelf.stockBase (cap*payload) m)
    (guardEnd : v.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤C.stopAt a)
    (failedEnd : v.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤v.failures.base) :
    let stamped:=v.failures.pass.apply ((guard C a).apply m)
    ∀ t : Tile z d, ∀j : Fin k×Bool,stockBits v.shelf.stockBase k stamped t j < v.shelf.table.size := by
  intro stamped t j
  let i : Commodity (Fin (2^z)) (2*rounds d+1) k:=.inr ((t.2,stageNumber t.1),j)
  let adr:=v.shelf.stockBase+PurchaseInventory.slot i
  have lo : adr < v.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k :=
    Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _
  have stamp:=v.failures.frame ((guard C a).apply m) adr (.inl (lo.trans_le failedEnd))
  have keep : (guard C a).apply m adr=m adr :=
    ProtocolRAMGeneratedWrite.frame_image (C.stopAt a) 1 (stop C.mesh C.modeAt a) m adr
      (.inl (lo.trans_le guardEnd))
  change (v.failures.pass.apply ((guard C a).apply m) adr).val < 2^v.shelf.tableBits
  rw [stamp,keep,span]
  exact ProtocolRAMPurchaseSampler.threshold_index (bounded i) width

/-- Both writes before the signed sweep preserve the live previous-stock band.
This local form also discharges the current event's own readiness while the
chronological stock bound is being proved. -/
theorem StripChart.Slab.frozen_threshold (s : StripChart.Boards z d k q depth)
    (b : StripDirectory.Boards z d k q digits ports) (headerEnd cap payload base : ℕ)
    (C : Chart (wordBits z d copies) q goods) (a : Attempt) (m : Shelf.Mem z d) (width : payload≤2^z)
    (bounded : StockBound.Bounded z (2*rounds d+1) k b.market.shelf.stockBase (cap*payload) m)
    (guardEnd : b.market.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤C.stopAt a)
    (failedEnd : b.market.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤b.market.failures.base) :
    let x:=((StripChart.Slab.forCap headerEnd cap).localize s b base).market
    let stamped:=x.failures.pass.apply ((guard C a).apply m)
    ∀v : Tile z d, ∀j : Fin k×Bool,stockBits x.shelf.stockBase k stamped v j < x.shelf.table.size := by
  exact Market.frozen_threshold _ cap payload C a m width rfl bounded guardEnd failedEnd

/-- Specialize to a named calendar event in the actual chronological run,
including saved-stock protection across every intervening trial. -/
theorem StockBound.Run.frozen_threshold {cap payload headerEnd base : ℕ} {start m : Shelf.Mem z d}
    {C : Chart (wordBits z d copies) q goods} {B : StockBound.Banks} {a : Attempt} {earlier later : List Event}
    (contract : StockBound.Run C B start z (2*rounds d+1) k (cap*payload))
    (entry : Slot C start (.attempt a) earlier later m) (s : StripChart.Boards z d k q depth)
    (b : StripDirectory.Boards z d k q digits ports) (width : payload≤2^z)
    (address : b.market.shelf.stockBase=B.previous C.mesh (.attempt a))
    (guardEnd : b.market.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤C.stopAt a)
    (failedEnd : b.market.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k≤b.market.failures.base) :
    let x:=((StripChart.Slab.forCap headerEnd cap).localize s b base).market
    let stamped:=x.failures.pass.apply ((guard C a).apply m)
    ∀v : Tile z d, ∀j : Fin k×Bool,stockBits x.shelf.stockBase k stamped v j < x.shelf.table.size := by
  apply StripChart.Slab.frozen_threshold s b headerEnd cap payload base C a m width _ guardEnd failedEnd
  rw [address]
  exact (contract.slot entry).1

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
