import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedFailurePopulation

namespace OAI
/-! # Original calendar resources at a dated paid-repair slot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseStage StockCommit StripDirectory PurchaseCT
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "FEE" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "st" => v.stamp P z width r banks src tab dst owners
local notation "phaseRows" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))

/-- Input resources on the original chronological run. All three memories used
by packet pricing will be read off the one installed public prefix in `init`. -/
structure RepairSlot where
  init : Memory W
  prior : List Event
  tail : List Event
  slot : Slot C init (.attempt a) prior tail entry
  resident : (H).Resident init
  stock : ℕ→ℕ
  initialPrices : InitialPrices P.joint z N k phaseRows stock init
  charged : (FEE).Resident init
  stockRun : StockBound.Run C (v.stockBanks P z width) init z N k (v.keepLimit*width)
  capacity : v.keepLimit*width≤P.joint.cap*P.joint.width
  layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (st a) v.keepLimit width
    ((G).base v.mesh (.attempt a))
  valid : accepted C (.attempt a) entry
  failed : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))=2
  large : v.widthFloor≤width
  positive : 0<width
  late : v.stripHeight≤z
  threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W
  letterFit : v.menu.alphabet<2^W
  rateRoom : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width<2^W

variable {v P z width r banks src tab dst owners a entry}
variable (s : v.RepairSlot P z width r banks src tab dst owners a entry)
local notation "g₀" => JointHeader.scores P.joint z N k
include s

theorem RepairSlot.event : Event.attempt a∈events v.mesh := by
  change Event.attempt a∈events (C).mesh
  rw [s.slot.events]
  simp

theorem RepairSlot.pages : v.RepairPages P z width r banks src tab dst owners a entry :=
  v.paid_row_pages_at_slot P z width r banks src tab dst owners a s.prior s.tail s.init entry s.slot
    s.resident s.stock s.initialPrices s.charged

theorem RepairSlot.limit (i : Commodity (Fin (2^z)) N k) : (entry ((A).stockAt a i)).val<(g₀).stride :=
  v.stock_stride_at_slot P z width r banks src tab dst owners bills a s.prior s.tail s.init entry s.slot s.stockRun s.capacity i

theorem RepairSlot.held (i : Commodity (Fin (2^z)) N k) :
    ((A).read (Succession v.mesh (.attempt a)).1 entry).bits i≤v.keepLimit*width := by
  have same : (Succession v.mesh (.attempt a)).1=a := by cases a <;> rfl
  rw [same]
  change (entry ((v.nativeAccount P z width bills).stockAt a i)).val≤_
  rw [v.stock_pointer P z width bills a i]
  have pointer := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh G P.joint.initial
    (v.emptyReserve P z width) a).1
  change (f a).market.shelf.stockBase=(v.stockBanks P z width).previous v.mesh (.attempt a) at pointer
  change (entry ((f a).market.shelf.stockBase+PurchaseInventory.slot i)).val≤_
  rw [pointer]
  exact (s.stockRun.slot s.slot).1 i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
