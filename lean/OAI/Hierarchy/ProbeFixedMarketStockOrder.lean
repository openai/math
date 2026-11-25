import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeMarketStockBounds

namespace OAI
/-! # The predecessor stock address at each actual market date -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT StripChart CoreBoard
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "deg" => 2^v.W
local notation "bits" => wordBits z deg copies
local notation "area" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "cells" => PurchaseInventory.footprint z (Stages z deg) k
local notation "market" => (fun a=> (fmt a).atTime v.mesh v.finish (v.basePhase width) a)

private theorem incoming_eq (a : Attempt) :
    (market a).shelf.stockBase=previousStock v.mesh P.joint.initial (publishedStock v.mesh area fmt) (.attempt a) :=
  (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh area P.joint.initial
    (v.emptyReserve P z width) a).1

theorem market_initial_floor : P.joint.initial≤(area).first :=
  initial_stock_floor (c:=v.mesh) (arena:=area) (f:=publishedStock v.mesh area fmt)
    (v.stock_padded_old P z width (.outer 0 0)) (v.incoming_eq P z width (.outer 0 0))

/-- Each attempt reads an earlier committed bank above the CT heap. -/
theorem market_stock_heap (a : Attempt) (initial : heapEnd z deg copies≤P.joint.initial) :
    heapEnd z deg copies≤(market a).shelf.stockBase := by
  rw [v.incoming_eq P z width a]
  exact previous_stock_floor v.mesh area fmt initial (initial.trans (v.market_initial_floor P z width))
    (v.stock_label P z width) (.attempt a)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
