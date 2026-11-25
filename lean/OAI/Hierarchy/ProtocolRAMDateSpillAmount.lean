import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout

namespace OAI
/-! # Reading commodity spill weights from the original dated output columns -/

namespace Hierarchy.ProtocolRAMDateSpillRank
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ProtocolRAM ProtocolRAM.RouteSettlement ProtocolRAM.Calendar
open scoped Fin.CommRing

variable {h N k W : ℕ}

/-- A dated output is laid out in ordinary inventory slot order. The rounded
binary capacity is used only for the bounded native lookup instruction. -/
def amountBank (h N k base : ℕ) : Bank :=
  ⟨base,ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint h N k)⟩

theorem amountBank_fits (base lo : ℕ) (endBefore :
    base+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)≤lo)
    (word : lo<2^W) : (amountBank h N k base).Fits W lo := by
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (endBefore.trans_lt word),endBefore⟩

theorem amountBank_read (base : ℕ) (m : Memory W) (c : Commodity (Fin (2^h)) N k)
    (word : PurchaseInventory.footprint h N k≤2^W) :
    actual (amountBank h N k base) m (PurchaseInventory.slot c)=
      (m (base+PurchaseInventory.slot c)).val := by
  have hi:=PurchaseInventory.slot_lt c
  change (m (base+(PurchaseInventory.slot c : Word W).val%
    ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k))).val=_
  rw [Fin.val_cast_of_lt (hi.trans_le word),Nat.mod_eq_of_lt (hi.trans (ProtocolRAMPurchaseSampler.lt_span _))]

/-- Repair settlement stores spill after the kept and held columns. -/
def attemptBank (h N k : ℕ) (a : StockCommit.Area) : Bank :=
  amountBank h N k (a.output+2*a.goods)

/-- Every signed feed lane belongs to one contiguous dated spill page. -/
def feedBank (L : FeedLayout h N k) : Bank := amountBank h N k L.overflow

theorem attempt_read (a : StockCommit.Area) (m : Memory W) (c : Commodity (Fin (2^h)) N k)
    (word : PurchaseInventory.footprint h N k≤2^W) :
    actual (attemptBank h N k a) m (PurchaseInventory.slot c)=
      (m (a.output+2*a.goods+PurchaseInventory.slot c)).val :=
  amountBank_read _ _ _ word

theorem feed_read (L : FeedLayout h N k) (m : Memory W) (c : Commodity (Fin (2^h)) N k)
    (word : PurchaseInventory.footprint h N k≤2^W) :
    actual (feedBank L) m (PurchaseInventory.slot c)=
      (m ((L.column ⟨PurchaseInventory.lane c,PurchaseInventory.lane_lt c⟩).overflow+
        (PurchaseInventory.record c).val)).val := by
  simpa [feedBank,FeedLayout.column,PurchaseInventory.slot,Nat.add_assoc] using
    amountBank_read L.overflow m c word

end Hierarchy.ProtocolRAMDateSpillRank

end OAI
