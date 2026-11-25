import OAI.Hierarchy.ProbeFixedBeforeTests
import OAI.Hierarchy.ProbeFixedDatedTests
import OAI.Hierarchy.ProbeFixedPurchasedArchiveBuffers

namespace OAI
/-! # Noncircular threshold admission from the live preceding chronology -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open PurchaseCT PurchaseFrozen PurchaseStage
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ) (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "fs" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "L" => JointHeader.scores P.joint z N k
local notation "phaseRows" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "raw[" a "," e "]" => (guard C a).apply e
local notation "cash" => v.stockBanks P z width

/-- The thresholds whose dimensions depend only on the selected public format. -/
structure TestWordRoom : Prop where
  addresses : (G).endAddress v.mesh<2^W
  precision : P.joint.precision=v.precision
  globalHeight : v.voteHeight≤z
  failureHeight : v.discrepancyScanHeight≤z
  cut : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W
  stride : (L).stride≤2^z
  capacity : v.keepLimit*width≤P.joint.cap*P.joint.width

section
variable (phase trial : ℕ)
local notation "ev" => Attempt.outer phase trial

private theorem payload_tests_before_by_amounts (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (amount : ∀ i, ((run C prior init) ((v.nativeAccount P z width bills).stockAt ev i)).val < (L).stride)
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  have onClock : Event.attempt ev ∈ events v.mesh := by rw [split]; simp
  have date := dateInTable_of_event v.mesh ev onClock
  have hot := v.date_time_positive ev date
  have hdr := v.prepared_guard_pages P z width r banks src tab dst owners ev prior init previous boot initialStock pages
  have summed := v.payload_discrepancy_scan P z width r banks src tab dst owners phase trial
    (run C prior init) date hot words.failureHeight hdr.1 hdr.2 amount
  have read := hdr.2
  rw [DeadlineROM.outer_price v.mesh v.finish (v.basePhase width) phase trial date] at read
  exact v.dated_tests_with_discrepancy P z width r banks src tab dst owners ev (run C prior init) onClock
    words.addresses words.precision words.globalHeight words.failureHeight words.cut words.stride market read amount summed

theorem payload_tests_before_of_bounded (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (old : StockBound.Bounded z N k ((cash).previous v.mesh (.attempt ev)) (v.keepLimit*width) (run C prior init))
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  exact v.payload_tests_before_by_amounts P z width r banks src tab dst owners phase trial
    prior tail init split previous boot initialStock pages
    (v.prepared_guard_stock_of_bounded P z width bills ev (run C prior init) old words.capacity) words market

theorem payload_tests_before (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (receipts : (cash).receipts v.mesh z N k (v.keepLimit*width) prior.length (run C prior init))
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  exact v.payload_tests_before_by_amounts P z width r banks src tab dst owners phase trial
    prior tail init split previous boot initialStock pages
    (v.prepared_guard_stock P z width r banks src tab dst owners bills ev prior tail init split receipts words.capacity) words market

end

section
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

private theorem purchased_tests_before_by_amounts (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (amount : ∀ i, ((run C prior init) ((v.nativeAccount P z width bills).stockAt ev i)).val < (L).stride)
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) (π : Equiv.Perm (Fin (2^z)))
    (headerLow : (h₀).stop≤(G).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader phase trial) (run C prior init) k) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  have onClock : Event.attempt ev∈events v.mesh := by rw [split]; simp
  have date := dateInTable_of_event v.mesh ev onClock
  have hot := v.date_time_positive ev date
  have hdr := v.prepared_guard_pages P z width r banks src tab dst owners ev prior init previous boot initialStock pages
  have archive := v.purchased_guard_archive P z width r banks src tab dst owners phase trial slice inner (run C prior init) π
    headerLow born
  have flags := v.purchased_guard_archive_flags P z width r banks src tab dst owners phase trial slice inner
    (run C prior init) π headerLow born
  have late : v.stripHeight ≤ z := (le_max_left _ _).trans words.failureHeight
  have summed := v.purchased_discrepancy_scan P z width r banks src tab dst owners phase trial slice inner
    (run C prior init) date hot words.failureHeight hdr.1 hdr.2 amount π archive.1 archive.2
    (fun j active => v.purchased_live_row P z width phase trial slice inner π
      born.stock born.phase born.price born.kind born.frozen raw[ev,run C prior init]
      flags (v.purchased_table_room z late).2.2.1 j active)
  have read := hdr.2
  rw [DeadlineROM.inner_price v.mesh v.finish (v.basePhase width) phase trial slice inner date.1 date.2] at read
  exact v.dated_tests_with_discrepancy P z width r banks src tab dst owners ev (run C prior init) onClock
    words.addresses words.precision words.globalHeight words.failureHeight words.cut words.stride market read amount summed

theorem purchased_tests_before_of_bounded (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (old : StockBound.Bounded z N k ((cash).previous v.mesh (.attempt ev)) (v.keepLimit*width) (run C prior init))
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) (π : Equiv.Perm (Fin (2^z)))
    (headerLow : (h₀).stop≤(G).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader phase trial) (run C prior init) k) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  exact v.purchased_tests_before_by_amounts P z width r banks src tab dst owners phase trial slice inner
    prior tail init split previous boot initialStock pages
    (v.prepared_guard_stock_of_bounded P z width bills ev (run C prior init) old words.capacity) words market π headerLow born

theorem purchased_tests_before (prior tail : List Event) (init : Memory W)
    (split : events v.mesh=prior++.attempt ev::tail) (previous : Calendar.mounted C prior init)
    (boot : (H).Resident init) (initialStock : ℕ→ℕ)
    (pages : InitialPrices P.joint z N k phaseRows initialStock init)
    (receipts : (cash).receipts v.mesh z N k (v.keepLimit*width) prior.length (run C prior init))
    (words : v.TestWordRoom P z width)
    (market : ((C).frozen ev).ready raw[ev,run C prior init]) (π : Equiv.Perm (Fin (2^z)))
    (headerLow : (h₀).stop≤(G).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader phase trial) (run C prior init) k) :
    TestsReady (repair C ev) (prepared C ev (run C prior init)) := by
  exact v.purchased_tests_before_by_amounts P z width r banks src tab dst owners phase trial slice inner
    prior tail init split previous boot initialStock pages
    (v.prepared_guard_stock P z width r banks src tab dst owners bills ev prior tail init split receipts words.capacity) words market π headerLow born

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
