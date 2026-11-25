import OAI.Hierarchy.ProbeFixedStockConservation
import OAI.Hierarchy.TaggedWireFixedGoodsChange

namespace OAI
/-! # Funding each measured debit using the preceding native stock word -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit PurchaseStage RepairHistogram
open scoped BigOperators Classical Fin.CommRing
set_option maxRecDepth 4096
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "bs" => v.stockBanks P z width
local notation "es" => events v.mesh
local notation "Good" => FeedLayout.Good z (Stages z (2^v.W)) k
local notation "Qty" => v.datedQuantity P z width r banks src tab dst owners
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (Native.wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)

include D in
theorem ReadbackRun.dated_pre_debit (B : RepairWordBounds v P z width)
    (n : ℕ) (on : n < (es).length) (a : Attempt) (atTrial : (es)[n] = .attempt a)
    {prior tail : List Event} {entry : Memory W} (cut : Slot C mem (.attempt a) prior tail entry)
    (i : Good) :
    let t := v.taskCommit P z width a
    let u := v.stage P z width r banks src tab dst owners a entry
    let tag := RepairHistogram.kind (goods:=t.goods) t.plan.bank t.columns u
    resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) (v.nativeSlots P z width a i) ≤
      PurchaseInventory.stock (DatedGoods.previous v.mesh bs n) entry i := by
  intro t u tag
  have funded := D.repair_pre_stock B a prior tail entry cut (v.nativeSlots P z width a i)
  dsimp only at funded
  rw [v.slot_index P z width a i,(v.attempt_stock_banks P z width a).1] at funded
  change _ ≤ (entry ((bs).previous v.mesh (.attempt a)+PurchaseInventory.slot i)).val at funded
  have same : (bs).previous v.mesh (.attempt a) = DatedGoods.previous v.mesh bs n := by
    rw [← atTrial]
    simp only [StockBound.Banks.previous, previousStock, position_at v.mesh on, DatedGoods.previous]
  rw [same] at funded
  exact funded

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
