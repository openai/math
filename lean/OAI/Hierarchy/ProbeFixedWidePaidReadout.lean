import OAI.Hierarchy.ProbeFixedWideForestBase
import OAI.Hierarchy.ProbeFixedPaidPortData
import OAI.Hierarchy.ProbeFixedPaidArchiveWord
import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeRetainedRows

namespace OAI
/-! # The paid arrays on both original native reporter tapes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open PurchaseFrozen RepairHistogram StockBound StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (h width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "E" => v.publicHeader P h width
local notation "A" => v.privateArena P h width
local notation "G" => v.stamp P h width r banks src tab dst owners
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "b" => (P).catalogue
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "coreEnd" => CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth
  (WideMemory.K h v.W) (packed).groups (WideMemory.H h v.W k v.wideJobs) (b).coreRows
variable (π : Equiv.Perm (Fin (2^h)))
local notation "seen[" m "]" => CoreRoute.Seen order v.radius groups packed socket v.depth π m


local notation "form" => v.nativeFormats P h width
local notation "st" => v.taskCommit P h width
local notation "pre" => v.stage P h width r banks src tab dst owners
local notation "keyPage" => Public.keyHead v.sampler ((P).routes.column) h v.W k v.depth
variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "days" => v.birthMarks P h width r banks src tab dst owners m
local notation "layout[" a "]" => TrialLayout C a (form a).pricedArea (form a).stockSource (G a) v.keepLimit width
  ((A).base v.mesh (.attempt a))

/-- The actual two reporter observation times share these original arrays, including
the five original heterogeneous DFS tables on each selected parent. -/
structure WidePaidReadout (out : Memory W) : Prop where
  base : v.WideForestBase h width π out
  ports : ∀(phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel) (key : Key h (2^v.W) k),
    (((S).outer phase trial).market.shelf).PortData v.sampler π v.depth key out
  archived : ∀(a : Attempt) (before : Memory W) (earlier later : List Event),
    Slot C m (.attempt a) earlier later before → layout[a] → ∀i : Fin (form a).pricedArea.occurrences,
    (out ((form a).pricedArea.direct+i.val)).val=if kind (goods:=(form a).pricedArea.goods) (st a).plan.bank
      (st a).columns (pre a before) i=none then installedBits (st a).columns (pre a before) i else 0

omit [Nonempty (Fin k)] in
theorem paid_initial_tables (boot : seen[m]) :
    Shelf.Geometry π m ∧ heapEnd h (2^v.W) copies≤(A).first ∧
      (keyPage).stop≤(A).first ∧ (keyPage).Loaded m := by
  have sourcePrefix:=v.wideGeometryPrefix h width
  have first:=v.catalyst_initial_le_first P h width
  have low : (keyPage).stop≤(A).first := (show (keyPage).stop≤coreEnd from
    (Public.borders v.sampler (P).routes.column h v.W k v.wideJobs v.depth).2.trans (Nat.le_add_right ..)).trans
      (sourcePrefix.2.2.trans first)
  exact ⟨fun i=>⟨_,boot.board.columns.geometry i⟩,sourcePrefix.2.1.trans first,low,boot.board.rom.keys⟩

omit [Nonempty (Fin k)] in
theorem wide_paid_run_reads (boot : seen[m]) («public» : (E).Resident m) (room : (A).endAddress v.mesh<2^W)
    (full : Calendar.mounted C (events v.mesh) m) :
    v.WidePaidReadout h width r banks src tab dst owners π m (run C (events v.mesh) m) := by
  obtain ⟨geo,heap,keyLow,keys⟩:=v.paid_initial_tables h width π m boot
  refine ⟨v.wide_forest_run_base h width r banks src tab dst owners π m boot «public» room full,?_,?_⟩
  · intro phase trial i
    exact v.terminal_port_data P h width r banks src tab dst owners m π phase trial full geo heap keyLow keys i
  · intro a entry earlier later slot layout i
    exact v.run_direct_credit P h width r banks src tab dst owners m entry a earlier later slot layout i

omit [Nonempty (Fin k)] in
theorem wide_paid_checkout_reads (flag : ℕ) (boot : seen[m]) («public» : (E).Resident m)
    (room : (A).endAddress v.mesh<2^W) (full : Calendar.mounted C (events v.mesh) m) (after : (A).endAddress v.mesh≤flag) :
    v.WidePaidReadout h width r banks src tab dst owners π m (checkedOut C flag m) := by
  obtain ⟨geo,heap,keyLow,keys⟩:=v.paid_initial_tables h width π m boot
  refine ⟨v.wide_forest_checkout_base h width r banks src tab dst owners π flag m boot «public» room full
    ((Nat.le_add_right ..).trans after),?_,?_⟩
  · intro phase trial i
    exact v.checkout_port_data P h width r banks src tab dst owners m π phase trial full geo heap keyLow keys flag after i
  · intro a entry earlier later slot layout i
    exact v.checkout_direct_credit P h width r banks src tab dst owners m entry a earlier later slot layout flag after i

omit [Nonempty (Fin k)] in
theorem paid_days_exclusive : Exclusive days := by
  intro i
  let day:=(outerDates v.mesh) i
  let mk:=v.frozenMarket P h width day.1 day.2
  let frozen:=v.frozenInput P h width r banks src tab dst owners m day.1 day.2
  change ∀t c c' x,x∈Shelf.catalogueMarks (observedMode C m day.1 day.2) mk.shelf mk.phase mk.temperature mk.kind frozen t c →
    x∈Shelf.catalogueMarks (observedMode C m day.1 day.2) mk.shelf mk.phase mk.temperature mk.kind frozen t c' → c=c'
  by_cases purchased : observedMode C m day.1 day.2=3
  · simpa [Shelf.catalogueMarks,purchased] using actualMarks_unique mk.shelf mk.phase mk.temperature mk.kind frozen (k:=k)
  · simp [Shelf.catalogueMarks,purchased]


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
