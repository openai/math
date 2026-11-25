import OAI.Hierarchy.ProbeFixedElectionPages
import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProbeFixedActivationParent
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProbeFixedQuoteFrames
import OAI.Hierarchy.ProbeFixedRepairBuffers
import OAI.Hierarchy.ProtocolRAMCalendarEconomicPrices
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster

namespace OAI
/-! # The real boot memory supplies the score and catalogue pages at every guarded ballot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ) (r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "H" => v.publicHeader P z width
local notation "arena" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "phaseRows" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)

local notation "FEE" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop

theorem row_pages_of_low (a : Attempt) (init m : Memory W) (resident : (H).Resident init)
    (stock : ℕ→ℕ) (mountedPrices : InitialPrices P.joint z N k phaseRows stock init)
    (constant : ∀x<(H).stop,m x=init x) : v.RowPages P z width a m := by
  have ord := economic_ordered F (v.sized (v.seed P z width) width) v.cost v.mesh P.joint P.catalogue P.routes
    v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  change (H).Ordered at ord
  have ports : (H).ports.stop ≤ (H).stop := CatalystArchive.economic_ports_end H ord
  constructor
  · apply EconomicHeader.upper_frame H ord resident
    · intro i
      exact (resident.ports i).frame (fun x _ high => constant x (high.trans_le (((H).ports.end_le i).trans ports)))
    · exact fun x _ high=>constant x high
  · apply (mountedPrices.scores (DeadlineROM.index v.mesh a)).transport
    intro x _ high
    have goalStop : JointHeader.stop P.joint z N k (DeadlineROM.count v.mesh)=(H).ports.base:=rfl
    have scoreBound : GlobalTests.stop (DeadlineROM.scorePage v.mesh g₀ z N k a) z N k ≤ (H).ports.base := by
      unfold DeadlineROM.scorePage
      rw [GlobalTests.page_stop,←goalStop]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (DeadlineROM.index v.mesh a).isLt) _
    exact constant x ((high.trans_le scoreBound).trans_le ((Nat.le_add_right ..).trans ports))

theorem slot_rows_low (a : Attempt) (prior tail : List Event) (init entry : Memory W)
    (cut : Slot C init (.attempt a) prior tail entry) (x : ℕ) (inside : x < (arena).first) :
    ((guard C a).apply entry) x=init x ∧
      PurchaseStage.postSnapshot ((C).layout a) (repair C a) (prepared C a entry) x=init x ∧
      v.stage P z width r banks src tab dst owners a entry x=init x := by
  have early (e : Event) : x < (arena).base v.mesh e := inside.trans_le (Nat.le_add_right ..)
  have keep (e : Event) := (v.event_prefix P z width r banks src tab dst owners e x (early e)).1
  have old : entry x=init x := by
    rw [←cut.entry]
    exact run_frame C prior init x cut.prefixReady (fun e _=>keep e)
  obtain ⟨first,mid,last⟩ := v.row_buffer_frame P z width r banks src tab dst owners a entry
    cut.currentReady x (early (.attempt a))
  exact ⟨first.trans old,mid.trans old,last.trans old⟩

theorem guard_pages_at_slot (a : Attempt) (prior tail : List Event) (init entry : Memory W)
    (cut : Slot C init (.attempt a) prior tail entry) (resident : (H).Resident init)
    (stock : ℕ→ℕ) (mountedPrices : InitialPrices P.joint z N k phaseRows stock init) :
    let m := (guard C a).apply entry
    (H).Resident m ∧ GlobalTests.Resident (DeadlineROM.scorePage v.mesh g₀ z N k a) z N k
      (phaseRows (DeadlineROM.index v.mesh a)) m := by
  have first : (H).stop ≤ (arena).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have pages := v.row_pages_of_low P z width a init _ resident stock mountedPrices
    (fun x h=>(v.slot_rows_low P z width r banks src tab dst owners a prior tail init entry cut x (h.trans_le first)).1)
  exact ⟨pages.header,pages.scores⟩

/-- All three runtime states obtain their tables from the mounted immutable
prefix, including the charged packet catalogue used at the actual stock commit. -/
theorem paid_row_pages_at_slot (a : Attempt) (prior tail : List Event) (init entry : Memory W)
    (cut : Slot C init (.attempt a) prior tail entry) (resident : (H).Resident init)
    (stock : ℕ→ℕ) (mountedPrices : InitialPrices P.joint z N k phaseRows stock init)
    (charged : (FEE).Resident init) : v.RepairPages P z width r banks src tab dst owners a entry := by
  have first : (H).stop ≤ (arena).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have feeEnd : (FEE).stop ≤ (arena).first := by
    change (v.emptyReserve P z width).base ≤ (arena).first
    exact (Nat.le_add_right ..).trans (v.emptyReserve_end_le_first P z width)
  have leftEnd : (FEE).payload.stop ≤ (FEE).stop := Nat.le_add_right ..
  have keep := v.slot_rows_low P z width r banks src tab dst owners a prior tail init entry cut
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact v.row_pages_of_low P z width a init _ resident stock mountedPrices (fun x h=>(keep x (h.trans_le first)).1)
  · exact v.row_pages_of_low P z width a init _ resident stock mountedPrices (fun x h=>(keep x (h.trans_le first)).2.1)
  · exact v.row_pages_of_low P z width a init _ resident stock mountedPrices (fun x h=>(keep x (h.trans_le first)).2.2)
  · exact charged.1.frame (fun x _ high=>(keep x ((high.trans_le leftEnd).trans_le feeEnd)).2.2)
  · exact charged.2.frame (fun x _ high=>(keep x (high.trans_le feeEnd)).2.2)

/-- The stock-index bound required by the quote table follows from the verified
chronological stock run. Only the numerical fit of the chosen public table is used. -/
theorem stock_stride_at_slot (bills : Event→WordRows) (a : Attempt) (prior tail : List Event)
    (init entry : Memory W) (cut : Slot C init (.attempt a) prior tail entry)
    (run : StockBound.Run C (v.stockBanks P z width) init z N k (v.keepLimit*width))
    (capacity : v.keepLimit*width≤P.joint.cap*P.joint.width)
    (i : Commodity (Fin (2^z)) N k) :
    (entry ((v.nativeAccount P z width bills).stockAt a i)).val < (g₀).stride := by
  let f := v.nativeFormats P z width a
  have pointer := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh arena P.joint.initial
    (v.emptyReserve P z width) a).1
  change f.market.shelf.stockBase=(v.stockBanks P z width).previous v.mesh (.attempt a) at pointer
  have bounded := (run.slot cut).1 i
  rw [v.stock_pointer P z width bills a i]
  change (entry (f.market.shelf.stockBase+PurchaseInventory.slot i)).val < P.joint.cap*P.joint.width+1
  rw [pointer]
  exact Nat.lt_succ_of_le (bounded.trans capacity)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
