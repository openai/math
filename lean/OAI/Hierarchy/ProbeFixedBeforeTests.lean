import OAI.Hierarchy.ProbeFixedGuardPages

namespace OAI
/-! # Score pages and stock receipts before testing the current trial -/

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
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "prices" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "bill" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop

private theorem before_low (a : Attempt) (prior : List Event) (init : Memory W)
    (mountedPrior : Calendar.mounted C prior init) (x : ℕ) (lower : x < (G).first) :
    ((guard C a).apply (run C prior init)) x = init x := by
  have keep (e : Event) := (v.event_prefix P z width r banks src tab dst owners e x
    (lower.trans_le (Nat.le_add_right ..))).1
  have safe : x < (C).stopAt a := (keep (.attempt a)).1
  have before : (run C prior init) x = init x := run_frame C prior init x mountedPrior (fun e _ => keep e)
  simpa only [Calendar.guard, Pass.apply, ProtocolRAM.image, ThreeFlat.RAM.fillSegment,
    not_le.mpr safe, false_and, ite_false] using before

/-- Transport the two actual public pages across the prefix and the current guard. -/
theorem prepared_guard_pages (a : Attempt) (prior : List Event) (init : Memory W)
    (mountedPrior : Calendar.mounted C prior init) (header : (H).Resident init) (initialStock : ℕ → ℕ)
    (initialPrices : InitialPrices P.joint z N k prices initialStock init) :
    let m := (guard C a).apply (run C prior init)
    (H).Resident m ∧ GlobalTests.Resident (DeadlineROM.scorePage v.mesh g₀ z N k a) z N k
      (prices (DeadlineROM.index v.mesh a)) m := by
  have first : (H).stop ≤ (G).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have pages := v.row_pages_of_low P z width a init _ header initialStock initialPrices
    (fun x hx => v.before_low P z width r banks src tab dst owners a prior init mountedPrior x (hx.trans_le first))
  exact ⟨pages.header,pages.scores⟩

theorem prepared_guard_charges (a : Attempt) (prior : List Event) (init : Memory W)
    (mountedPrior : Calendar.mounted C prior init) (paid : (bill).Resident init) :
    (bill).Resident ((guard C a).apply (run C prior init)) := by
  have endFee : (bill).stop ≤ (G).first := by
    change (v.emptyReserve P z width).base ≤ (G).first
    exact (Nat.le_add_right ..).trans (v.emptyReserve_end_le_first P z width)
  have left : (bill).payload.stop ≤ (bill).stop := Nat.le_add_right ..
  constructor
  · exact paid.1.frame (fun x _ h => v.before_low P z width r banks src tab dst owners a prior init
      mountedPrior x (h.trans_le (left.trans endFee)))
  · exact paid.2.frame (fun x _ h => v.before_low P z width r banks src tab dst owners a prior init
      mountedPrior x (h.trans_le endFee))

/-- A single chronological bound on the previous publication suffices to index
its stock words in the public scalar table. -/
theorem prepared_guard_stock_of_bounded (bills : Event → WordRows) (a : Attempt) (entry : Memory W)
    (old : StockBound.Bounded z N k ((v.stockBanks P z width).previous v.mesh (.attempt a)) (v.keepLimit*width) entry)
    (capacity : v.keepLimit*width ≤ P.joint.cap*P.joint.width) (i : Commodity (Fin (2^z)) N k) :
    (entry ((v.nativeAccount P z width bills).stockAt a i)).val < (g₀).stride := by
  let f := v.nativeFormats P z width a
  have ptr := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh G P.joint.initial
    (v.emptyReserve P z width) a).1
  change f.market.shelf.stockBase=(v.stockBanks P z width).previous v.mesh (.attempt a) at ptr
  rw [v.stock_pointer P z width bills a i]
  change (entry (f.market.shelf.stockBase+PurchaseInventory.slot i)).val < P.joint.cap*P.joint.width+1
  rw [ptr]
  exact Nat.lt_succ_of_le ((old i).trans capacity)

/-- The last publication before the current event is already covered by the
stock receipts for this prefix. -/
theorem prepared_guard_stock (bills : Event → WordRows) (a : Attempt) (prior tail : List Event)
    (init : Memory W) (split : events v.mesh = prior ++ .attempt a :: tail)
    (receipts : (v.stockBanks P z width).receipts v.mesh z N k (v.keepLimit*width) prior.length (run C prior init))
    (capacity : v.keepLimit*width ≤ P.joint.cap*P.joint.width) (i : Commodity (Fin (2^z)) N k) :
    ((run C prior init) ((v.nativeAccount P z width bills).stockAt a i)).val < (g₀).stride := by
  have small : prior.length < (events v.mesh).length := by rw [split,List.length_append,List.length_cons]; omega
  have atIndex : (events v.mesh)[prior.length] = .attempt a := by
    simp [split,List.getElem_append_right (Nat.le_refl prior.length)]
  have ordinal : position v.mesh (.attempt a) = prior.length := by
    rw [←atIndex]; exact position_at v.mesh small
  exact v.prepared_guard_stock_of_bounded P z width bills a (run C prior init)
    ((v.stockBanks P z width).previous_at v.mesh (.attempt a) ordinal receipts) capacity i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
