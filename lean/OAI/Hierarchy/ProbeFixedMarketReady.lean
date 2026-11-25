import OAI.Hierarchy.ProbeMarketShelfRoom
import OAI.Hierarchy.ProbeFixedMarketStockOrder
import OAI.Hierarchy.ProbeFixedMarketShelfFields

namespace OAI
/-! # Geometry of the actual input-dependent sampler used at every attempt -/

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

/-- The incoming pointer names the real output of the preceding attempt or
feed. Its whole inventory precedes the current signed threshold table. -/
theorem market_inventory (a : Attempt) :
    (market a).shelf.stockBase+PurchaseInventory.footprint z (2*rounds deg+1) k≤(market a).shelf.thresholdBase ∧
    (market a).shelf.table.base+(market a).shelf.table.size≤(market a).shelf.firstBase := by
  let seed:=v.seed P z width
  let sizes:=v.sized seed width
  let base:=(area).base v.mesh (.attempt a)
  obtain ⟨threshold,amount,first,_⟩:=v.market_shelf_fields P z width a
  have old:=v.stock_padded_old P z width a
  have limit:=(ProtocolRAMPurchaseSampler.lt_span cells).le
  have stages : Stages z deg=2*rounds deg+1 := template_length ..
  constructor
  · rw [←stages,threshold]
    exact ((Nat.add_le_add_left limit _).trans old).trans
      ((Nat.le_add_right base (Slab.selectorSpan sizes)).trans (Nat.le_add_right _ (Slab.failureSpan sizes)))
  · change (market a).shelf.thresholdBase+(market a).shelf.table.size≤(market a).shelf.firstBase
    rw [threshold,amount,first]
    exact le_rfl

theorem market_stock_end (a : Attempt) (t : StageAt z deg) (j : Fin (2*k)) :
    ((market a).shelf.stock t j).base+((market a).shelf.stock t j).size≤(market a).shelf.firstBase :=
  Boot.shelf_stock_end _ (v.market_inventory P z width a).1 (v.market_inventory P z width a).2 t j

theorem market_dimensions (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (initial : heapEnd z deg copies≤P.joint.initial) (capacity : (area).endAddress v.mesh<2^bits)
    (height : 2*k+v.sampler.degree≤z) (i : Key z deg k) :
    Ready (market a).sampler (PurchaseFrozen.stage i) ((market a).shelf.cfg (market a).sampler (market a).depth i) := by
  have table:=v.market_inventory P z width a
  have large : z<2^bits := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide)
    (by rw [wordBits_linear];omega))
  have directions : 2*k<2^bits := ((Nat.le_add_right _ _).trans height).trans_lt large
  have degree : (market a).sampler.degree≤2^bits := by
    rw [(v.market_shelf_fields P z width a).2.2.2]
    exact ((Nat.le_add_left _ _).trans height).trans large.le
  exact Boot.shelf_dimensions _ Nat.one_le_two_pow (v.market_stock_heap P z width a initial) table.1 table.2
    (v.market_capacity P z width a scheduled capacity) directions degree i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
