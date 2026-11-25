import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock

namespace OAI
/-! # No reserve feed or charge after an observed non-purchase -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners

private theorem same_inventory {I : Type*} {x y : Inventory I} (h : ∀i,x.bits i=y.bits i) (p : x.paid=y.paid) : x=y := by
  cases x with | mk b p₁ => cases y with | mk c p₂ => exact congrArg₂ Inventory.mk (funext h) p

/-- The clock still executes the inner feed after its outer date has failed to
purchase. Its archived mode disables every reserve addition. The actual bounded
active word is reissued unchanged and all spill charges have width zero. -/
private theorem quiet_feed_of_stored (mem : Memory W) (stock : Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (wide : 4≤ 2^W)
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (G).first)
    (addressRoom : (G).endAddress v.mesh < 2^W) (budget : v.keepLimit*width < 2^W)
    (p a j : ℕ) (hp : p < v.mesh.inject+v.mesh.cool) (ha : a < v.mesh.outerFuel) (hj : j < v.mesh.reserveSteps)
    (observed : (innerState C mem p a j v.mesh.innerFuel ((C).modeAt (.outer p a))).val=observedMode C mem p a)
    (idle : observedMode C mem p a ≠ 3) : (A).inner C mem p a (j+1) 0=(A).inner C mem p a j v.mesh.innerFuel := by
  let e : Event:=.feed (.inner p a j)
  let L:=FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit (.inner p a j)
  let entry:=innerState C mem p a j v.mesh.innerFuel
  let out:=after C e entry
  let next:=innerState C mem p a (j+1) 0
  have reached : next=out := reserve_succ C mem p a j
  have live : e∈events v.mesh := innerFeed_occurs v.mesh hp ha hj
  obtain ⟨_,atFeed⟩:=inner_feed_slot C mem p a j hp ha hj stock.mounted_all
  have current : entry ((C).modeAt (.outer p a))≠3 := by
    intro buy
    apply idle
    change (entry ((C).modeAt (.outer p a))).val=_ at observed
    rw [buy,show (3:Word W).val=3 from Fin.val_cast_of_lt (a := 3) wide] at observed
    exact observed.symm
  obtain ⟨before,room⟩ := v.stock_feed P z width r banks src tab dst owners (.inner p a j) live initialRoom addressRoom
  have rows : 2^z ≤ 2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  have words (i : Commodity (Fin (2^z)) N k) : (out (L.kept+PurchaseInventory.slot i)).val=PurchaseInventory.stock L.active entry i ∧
      (out (L.overflow+PurchaseInventory.slot i)).val=0 :=
    L.idle_rows C p a j entry rfl before room budget rows i current ((stock.slot atFeed).1 i)
  apply same_inventory
  · intro i
    change (next ((A).stockAt (.inner p a (j+1) 0) i)).val=(entry ((A).stockAt (.inner p a j v.mesh.innerFuel) i)).val
    rw [reached]
    have target : (A).stockAt (.inner p a (j+1) 0) i=L.kept+PurchaseInventory.slot i :=
      stockAt_inner_next v.mesh G f P.joint.initial width v.keepLimit p a j i hp ha hj
    have source : (A).stockAt (.inner p a j v.mesh.innerFuel) i=L.active+PurchaseInventory.slot i :=
      stockAt_inner_end v.mesh G f P.joint.initial width v.keepLimit p a j i
    rw [target,source]
    exact (words i).1
  · let issued:=v.issued P z width r banks src tab dst owners
    have spill : (issued e).bill width out=0 := by
      change (spillRows L (fun _=>0) (fun i _=>routeCap N v.radius (PurchaseInventory.lane i))).bill width out=0
      simp [spillRows,WordRows.bill_ports,ChargeWord.value,fun i=>(words i).2]
    have paid := v.append_paid P z width r banks src tab dst owners e entry live atFeed.currentReady
    change ((A).read (.inner p a (j+1) 0) out).paid=((A).read (.inner p a j v.mesh.innerFuel) entry).paid+(issued e).bill width out at paid
    change ((A).read (.inner p a (j+1) 0) next).paid=((A).read (.inner p a j v.mesh.innerFuel) entry).paid
    simpa only [reached,spill,add_zero] using paid

theorem quiet_feed (mem : Memory W) (stock : Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (archive : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool))
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (G).first)
    (addressRoom : (G).endAddress v.mesh < 2^W) (budget : v.keepLimit*width < 2^W)
    (p a j : ℕ) (hp : p < v.mesh.inject+v.mesh.cool) (ha : a < v.mesh.outerFuel) (hj : j < v.mesh.reserveSteps)
    (idle : observedMode C mem p a ≠ 3) : (A).inner C mem p a (j+1) 0=(A).inner C mem p a j v.mesh.innerFuel := by
  have floor (e : Event) (x : ℕ) (hx : x < (G).base v.mesh e) := (v.event_prefix P z width r banks src tab dst owners e x hx).1
  exact v.quiet_feed_of_stored P z width r banks src tab dst owners mem stock archive.wide initialRoom addressRoom budget p a j hp ha hj
    (mode_at_feed C G mem p a j stock.mounted_all archive hp ha hj floor (v.stock_mode_room P z width (.outer p a))) idle

theorem quiet_feed_local (mem : Memory W) (stock : Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (G).first)
    (addressRoom : (G).endAddress v.mesh < 2^W) (budget : v.keepLimit*width < 2^W)
    (p a j : ℕ) (hp : p < v.mesh.inject+v.mesh.cool) (ha : a < v.mesh.outerFuel) (hj : j < v.mesh.reserveSteps)
    (layout : TrialLayout C (.outer p a) (f (.outer p a)).pricedArea (f (.outer p a)).stockSource
      (v.stamp P z width r banks src tab dst owners (.outer p a)) v.keepLimit width ((G).base v.mesh (.attempt (.outer p a))))
    (idle : observedMode C mem p a ≠ 3) : (A).inner C mem p a (j+1) 0=(A).inner C mem p a j v.mesh.innerFuel := by
  have floor (e : Event) (x : ℕ) (hx : x < (G).base v.mesh e) := (v.event_prefix P z width r banks src tab dst owners e x hx).1
  exact v.quiet_feed_of_stored P z width r banks src tab dst owners mem stock layout.window.wide initialRoom addressRoom budget p a j hp ha hj
    (mode_at_feed_local C G mem p a j stock.mounted_all layout.window.wide hp ha hj layout.board layout.positive floor
      (v.stock_mode_room P z width (.outer p a))) idle

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
