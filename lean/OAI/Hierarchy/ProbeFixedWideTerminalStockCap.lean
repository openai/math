import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProbeFixedTerminalStock

namespace OAI
/-! # The last real stock publication at the signed checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (h width : ℕ)
set_option quotPrecheck false
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "A" => v.privateArena P h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "pages" => v.stockBanks P h width
local notation "finish" => Attempt.outer (v.mesh.inject+v.mesh.cool) 0

/-- The bank used by the terminal route reporter is exactly the active
predecessor at the complete calendar prefix. The final verdict writes above it. -/
theorem terminal_stock_at_checkout {u q' goods : ℕ} (C : Chart u q' goods) (m : Memory u)
    (mesh : C.mesh=v.mesh) (fit : (A).endAddress v.mesh<2^u)
    (run : StockBound.Run C pages m h N k (v.keepLimit*width))
    (i : Commodity (Fin (2^h)) N k) :
    RouteSettlement.actual stock (checkedOut C ((A).endAddress v.mesh) m) (PurchaseInventory.slot i)≤
      v.keepLimit*width := by
  let last:=(events C.mesh).length
  have atEnd := (run last le_rfl).2
  have cursor : position C.mesh (.attempt finish)=last := by
    dsimp only [last]
    rw [mesh,event_count]
    simp [position,trialBase,phaseSize,trialSize,sliceSize]
  have active:=(pages).previous_at C.mesh (.attempt finish) cursor atEnd i
  have state : StockBound.state C m last=Calendar.run C (events C.mesh) m := by
    simp [StockBound.state,last]
  rw [state] at active
  have prior : (pages).previous C.mesh (.attempt finish)=(stock).base := by rw [mesh];rfl
  change ((Calendar.run C (events C.mesh) m) ((pages).previous C.mesh (.attempt finish)+PurchaseInventory.slot i)).val≤_ at active
  rw [prior] at active
  have row : PurchaseInventory.slot i<(stock).size :=
    (PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _)
  have low : (stock).base+PurchaseInventory.slot i<(A).endAddress v.mesh :=
    (Nat.add_lt_add_left row (stock).base).trans_le (v.fixedTerminalStock_end P h width)
  have key : PurchaseInventory.slot i<2^u :=
    (Nat.le_add_left ..).trans_lt (low.trans fit)
  simp only [RouteSettlement.actual,Bank.read,Fin.val_cast_of_lt key,Nat.mod_eq_of_lt row,checkedOut]
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl low)]
  exact active

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
