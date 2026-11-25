import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProtocolRAMCalendarStockOrigin
import OAI.Hierarchy.ProtocolRAMCalendarStockTables

namespace OAI
/-! # Capped stock on the actual fixed chart and its native reserve operands -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "A" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners

def stockBanks := pricedBanks v.mesh A f P.joint.initial (v.emptyReserve P z width).base

theorem stock_mode_before (a : Attempt) : (f a).board.modeOut < (f a).labelStart := by
  let s:=f a
  change PostLayout.column s.maskStart s.indexBits s.market.rows 2 <
      PostLayout.column s.maskStart s.indexBits s.market.rows (17+3*_+s.checkedBoard.batch.quotes.length)+1
  apply Nat.lt_succ_of_le
  unfold PostLayout.column
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

theorem stock_mode_room (a : Attempt) : (f a).board.modeOut+1 ≤ (A).base v.mesh (.attempt a)+(A).stride :=
  (show (f a).board.modeOut+1 ≤ (f a).labelStart from v.stock_mode_before P z width a).trans (((Nat.le_add_right ..).trans (f a).chargeColumns.1).trans (v.attempt_room P z width a))

theorem stock_order (a : Attempt) : (A).base v.mesh (.attempt a) ≤ (f a).market.failures.base ∧
    (A).base v.mesh (.attempt a) ≤ (f a).market.shelf.firstBase ∧ (A).base v.mesh (.attempt a) ≤ (f a).testsStart :=
  v.posted_attempt_order P z width a

theorem stock_label (a : Attempt) : (A).base v.mesh (.attempt a) ≤ (f a).labelStart := by
  let s:=f a
  have base:=(v.stock_order P z width a).2.2
  change (A).base v.mesh (.attempt a) ≤ s.testsStart at base
  have tests : s.testsStart ≤ s.maskStart := by unfold Format.maskStart PostLayout.afterTests;omega
  have cut : s.maskStart ≤ PostLayout.startColumns s.maskStart s.indexBits s.market.rows :=
    ((Nat.le_add_right s.maskStart (2^s.indexBits)).trans (Nat.le_add_right _ s.market.rows)).trans
      (Nat.le_add_right _ 2)
  have cert : PostLayout.startColumns s.maskStart s.indexBits s.market.rows ≤ s.board.verdict := Nat.le_add_right ..
  change _ ≤ s.board.verdict+1
  omega

theorem stock_post_span (a : Attempt) :
    (f a).pricedArea.output+(f a).pricedArea.goods+PurchaseInventory.footprint z N k ≤ (A).base v.mesh (.attempt a)+(A).stride := by
  have count : (f a).pricedArea.goods=PurchaseInventory.footprint z N k := by cases a <;> rfl
  have h:=v.attempt_room P z width a
  change (f a).pricedArea.output+3*(f a).pricedArea.goods ≤ _ at h
  omega

theorem stock_feed (boundary : Boundary) (onClock : Event.feed boundary∈events v.mesh)
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (A).first)
    (addressRoom : (A).endAddress v.mesh < 2^W) :
    let L:=FeedLayout.atEvent («N»:=N) v.mesh A f P.joint.initial width v.keepLimit boundary
    L.Before v.mesh (C).modeAt boundary ∧ L.stop < 2^W :=
  ⟨FeedLayout.atEvent_before v.mesh A f P.joint.initial width v.keepLimit boundary initialRoom
      (v.stock_post_span P z width) (v.stock_mode_room P z width) (v.feed_room P z width),
    FeedLayout.atEvent_fits v.mesh A f P.joint.initial width v.keepLimit boundary onClock (v.feed_room P z width) addressRoom⟩

/-- The native stock ceiling and event readiness are established together. Each
trial receives the actual active bank and, for an inner date, the authentic
outer purchase's saved bank. The static port header and half table refer to the
original tape throughout. -/
theorem native_stock (start fixture : Memory W)
    (balance : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock P.joint.initial start i=0)
    (vacant : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock (v.emptyReserve P z width).base start i=0)
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (A).first)
    (addressRoom : (A).endAddress v.mesh < 2^W) (budget : v.keepLimit*width < 2^W)
    (boards : ∀a,Event.attempt a∈events v.mesh →
       TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)) ∧
       Original (f a) (g a) (StripChart.start B a) (A).first start fixture)
    (reachable : ∀a,Event.attempt a∈events v.mesh →
      let j:=position v.mesh (.attempt a)
      let m:=state C start j
      Calendar.mounted C ((events v.mesh).take j) start →
      Bounded z N k ((v.stockBanks P z width).previous v.mesh (.attempt a)) (v.keepLimit*width) m →
      Bounded z N k ((v.stockBanks P z width).reserve (.attempt a)) (v.keepLimit*width) m → ready C (.attempt a) m) :
    Run C (v.stockBanks P z width) start z N k (v.keepLimit*width) := by
  let cells := PurchaseInventory.footprint z N k
  have count (a : Attempt) : (f a).pricedArea.goods=cells := by cases a <;> rfl
  have reserve : (v.emptyReserve P z width).base+cells ≤ (A).first := by
    have size : cells ≤ (v.emptyReserve P z width).size := (ProtocolRAMPurchaseSampler.lt_span cells).le
    exact (Nat.add_le_add_left size _).trans (v.emptyReserve_end_le_first P z width)
  have spans := v.feed_room P z width
  apply priced_static v.mesh v.finish (v.basePhase width) A f f P.joint.initial (v.emptyReserve P z width).base width v.keepLimit
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase (StripChart.start B)
    (fun a => (StripChart.header F B a).fieldTerm) (StripChart.id F B P.catalogue) start fixture balance vacant
    (by omega) reserve (v.stock_order P z width) (fun _=>rfl) (fun a=>(count a).ge) (v.stock_post_span P z width) (by omega) budget
  · exact fun a=>StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh A P.joint.initial (v.emptyReserve P z width) a
  · exact fun boundary onClock=>v.stock_feed P z width r banks src tab dst owners boundary onClock initialRoom addressRoom
  · exact boards
  · exact reachable

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
