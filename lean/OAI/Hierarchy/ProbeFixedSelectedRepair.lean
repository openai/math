import OAI.Hierarchy.ProbeFixedSelectedEconomy

namespace OAI
/-! # The actual payload and purchased mode-two repair receipts -/

noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory CoreBoard
open scoped BigOperators Classical
attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners

local notation "N₀" => Stages z (2^v.W)
variable [Nonempty (Fin k)]

section Account
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- The two dated account states and numerical parameters of the failed-row receipt. -/
@[reducible]
private def failed_packet_account (a : Attempt) (entry : Memory W) (time : ℝ) : Type :=
  (A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin time
    ((A).read (Succession v.mesh (.attempt a)).1 entry)
    ((A).read (Succession v.mesh (.attempt a)).2 (after C (.attempt a) entry))

variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
  (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) a
    (v.nativeFormats P z width a).pricedArea (v.nativeFormats P z width a).stockSource
    (v.stamp P z width r banks src tab dst owners a) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt a)))
  (run : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt a) entry)
  (ports : PortPlan (v.taskCommit P z width a) (v.ballot P z width r banks src tab dst owners a)
    (v.stage P z width r banks src tab dst owners a entry) (v.nativeFormats P z width a).market.rows)
local notation "tape" => v.selectedTape P z width r banks src tab dst owners a entry layout run ports

/-- Apply the row bounds on the dated tape that supplies the two stock inequalities. -/
private def failed_packet_of_bounds (time : ℝ) (nominal : Fin (f a).market.rows → ℕ)
    (positive : 0<width) (scheduled : Event.attempt a∈events v.mesh)
    (failed : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a)
      (repair C a) (prepared C a entry))=2)
    (funded : ∀ i : Fin (st a).goods, resourceBits (tape).kind (tape).take i ≤
      ((input a entry) ((st a).plan.bank.base+i.val)).val)
    (fits : ∀ i : Fin (st a).goods, ((input a entry) ((st a).plan.bank.base+i.val)).val +
      resourceBits (tape).kind (tape).put i < 2^W)
    (many : v.loss*(2^z:ℕ) ≤ (tape).selected.card)
    (bounds : v.SelectedBounds P z width r banks src tab dst owners a entry layout run ports time nominal) :
    v.failed_packet_account P z width r banks src tab dst owners a entry time := by
  obtain ⟨sizes, quotes, curve⟩ := bounds
  exact v.failed_packets P z width r banks src tab dst owners a entry layout run ports time nominal positive
    scheduled failed funded fits many sizes quotes curve

/-- Consumption is paid by the old bank, and installed bits obey the catalogue cap. -/
private def failed_stage_charges {w : ℕ} (c : StockCommit) (mem : Memory w) (cap : ℕ) : Prop :=
  ∀ i : Fin c.goods,
    resourceBits (RepairHistogram.kind c.plan.bank c.columns mem)
        (consumedBits (n:=c.occurrences) c.columns mem) i ≤ (mem (c.plan.bank.base+i.val)).val ∧
      resourceBits (RepairHistogram.kind c.plan.bank c.columns mem)
        (installedBits (n:=c.occurrences) c.columns mem) i ≤ cap

omit [Nonempty (Fin k)] in
/-- The actual stock pointer and the catalogue cap give both bounds on the dated tape. -/
private theorem failed_packet_spending (scheduled : Event.attempt a∈events v.mesh)
    (stock : ∀ i : Commodity (Fin (2^z)) N₀ k,
      ((A).read (Succession v.mesh (.attempt a)).1 entry).bits i ≤ v.keepLimit*width)
    (rateRoom : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width < 2^W)
    (charges : failed_stage_charges (st a) (input a entry) (v.menu.maximum*v.menu.copiesAt v.copyScale width)) :
    (∀ i : Fin (st a).goods, resourceBits (tape).kind (tape).take i ≤
      ((input a entry) ((st a).plan.bank.base+i.val)).val) ∧
    (∀ i : Fin (st a).goods, ((input a entry) ((st a).plan.bank.base+i.val)).val +
      resourceBits (tape).kind (tape).put i < 2^W) := by
  have observed := v.repair_stock P z width r banks src tab dst owners a entry scheduled run layout
  refine ⟨fun i => (charges i).1, ?_⟩
  intro i
  have old := (observed.1 i).symm.le.trans (stock ((v.nativeSlots P z width a).symm i))
  exact (Nat.add_le_add old (charges i).2).trans_lt rateRoom

end Account

section Payload
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (Attempt.outer phase trial)
    (v.nativeFormats P z width (Attempt.outer phase trial)).pricedArea (v.nativeFormats P z width (Attempt.outer phase trial)).stockSource
    (v.stamp P z width r banks src tab dst owners (Attempt.outer phase trial)) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt (Attempt.outer phase trial))))
  (run : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (Attempt.outer phase trial)) entry)
include layout run in
omit [Nonempty (Fin k)] in
/-- The prepared strip uses the mounted chart and broadcast room of its actual date. -/
private theorem payload_failed_room :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem ∧
      BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem ∧
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted]
  exact ⟨v.entered P z width r banks src tab dst owners ev entry run,
    fresh_broadcastRoom (f ev).pricedArea (f ev).stockSource (b ev) layout.inputs layout.window.room⟩

local notation "mount" => (v.payload_failed_room P z width r banks src tab dst owners phase trial entry fitted layout run).1
local notation "bc" => (v.payload_failed_room P z width r banks src tab dst owners phase trial entry fitted layout run).2
local notation "links" => v.printedCharge P z width ev
local notation "treeCost" => (fun (_ : Fin (f ev).market.rows) (_ : ℕ) => v.cost.atAttempt ev)
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout run π
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "bs" => v.nativeBoards P z width
local notation "menu" => payloadMenu F N₀ k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

include layout in
omit [Nonempty (Fin k)] in
/-- Read the paid and installed commodity totals at this strip's physical locations. -/
private theorem payload_failed_charges (placed : (x).Placed) :
    failed_stage_charges (st ev) (input ev entry) (v.menu.maximum*v.menu.copiesAt v.copyScale width) := by
  have numeric := v.catalogue_words (v.seed P z width) width
  have maximum : (x).board.maxWidth=v.menu.maximum := numeric.2.1
  have copiesEq : (x).board.copies=v.menu.copiesAt v.copyScale width := numeric.2.2
  have credit (i : Fin (x).raw.coordinates) :=
    Nat.le_trans ((x).credit_bound placed i) (congrArg₂ Nat.mul maximum copiesEq).le
  obtain ⟨site,reads⟩ := placed
  have seed (i : Fin (x).raw.coordinates) :
      (x).form.stockSource.old.read (x).mem (i.val:Word W)=(x).mem ((x).form.pricedArea.start+i.val) :=
    stage_seed_word_prefix (f ev).pricedArea (f ev).stockSource (g ev)
      (postOutput ((C).layout ev) (repair C ev) (prepared C ev entry))
      (layout.window.old.trans layout.window.label)
      ((Nat.le_add_left _ _).trans (Nat.le_of_lt (x).bankFit)) layout.window.capacity.1 i
  have paid : failed_stage_charges (fresh (x).form.pricedArea (x).form.stockSource) (x).mem
      (v.menu.maximum*v.menu.copiesAt v.copyScale width) :=
    fun i => ⟨(x).funded site reads seed i,credit i⟩
  rw [v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted] at paid
  exact paid

attribute [local irreducible] neighborhood

def payload_failed_packets (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ))))
    (scheduled : Event.attempt ev∈events v.mesh)
    (failed : AttemptGate.actual (repair C ev).policy (postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry))=2)
    (many : v.loss*(2^z:ℕ) ≤ (T).selected.card)
    (stock : ∀ i : Commodity (Fin (2^z)) N₀ k, ((A).read (Succession v.mesh (.attempt ev)).1 entry).bits i ≤ v.keepLimit*width)
    (rateRoom : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width < 2^W) :
    v.failed_packet_account P z width r banks src tab dst owners ev entry time :=
  let spending := v.failed_packet_spending P z width r banks src tab dst owners ev entry layout run π scheduled stock rateRoom
    (v.payload_failed_charges P z width r banks src tab dst owners phase trial entry fitted layout placed)
  v.failed_packet_of_bounds P z width r banks src tab dst owners ev entry layout run π time (x).nominal hw
    scheduled failed spending.1 spending.2 many
    (v.payload_selected_bounds P z width r banks src tab dst owners phase trial entry fitted layout run
      time timeMin hw large letterFit base table resident placed words)

end Payload
section Purchased
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (Attempt.inner phase trial slice inner)
    (v.nativeFormats P z width (Attempt.inner phase trial slice inner)).pricedArea (v.nativeFormats P z width (Attempt.inner phase trial slice inner)).stockSource
    (v.stamp P z width r banks src tab dst owners (Attempt.inner phase trial slice inner)) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt (Attempt.inner phase trial slice inner))))
  (run : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (Attempt.inner phase trial slice inner)) entry)
include layout run in
omit [Nonempty (Fin k)] in
/-- The prepared strip uses the mounted chart and broadcast room of its actual date. -/
private theorem purchased_failed_room :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem ∧
      BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem ∧
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted]
  exact ⟨v.entered P z width r banks src tab dst owners ev entry run,
    fresh_broadcastRoom (f ev).pricedArea (f ev).stockSource (b ev) layout.inputs layout.window.room⟩

local notation "mount" => (v.purchased_failed_room P z width r banks src tab dst owners phase trial slice inner entry fitted layout run).1
local notation "bc" => (v.purchased_failed_room P z width r banks src tab dst owners phase trial slice inner entry fitted layout run).2
local notation "links" => v.printedCharge P z width ev
local notation "treeCost" => (fun (_ : Fin (f ev).market.rows) (_ : ℕ) => v.cost.atAttempt ev)
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout run π
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "bs" => v.nativeBoards P z width
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

include layout in
omit [Nonempty (Fin k)] in
/-- Read the paid and installed commodity totals at this strip's physical locations. -/
private theorem purchased_failed_charges (placed : (x).Placed) :
    failed_stage_charges (st ev) (input ev entry) (v.menu.maximum*v.menu.copiesAt v.copyScale width) := by
  have numeric := v.catalogue_words (v.seed P z width) width
  have maximum : (x).board.maxWidth=v.menu.maximum := numeric.2.1
  have copiesEq : (x).board.copies=v.menu.copiesAt v.copyScale width := numeric.2.2
  have credit (i : Fin (x).raw.coordinates) :=
    Nat.le_trans ((x).credit_bound placed i) (congrArg₂ Nat.mul maximum copiesEq).le
  obtain ⟨site,reads⟩ := placed
  have seed (i : Fin (x).raw.coordinates) :
      (x).form.stockSource.old.read (x).mem (i.val:Word W)=(x).mem ((x).form.pricedArea.start+i.val) :=
    stage_seed_word_prefix (f ev).pricedArea (f ev).stockSource (g ev)
      (postOutput ((C).layout ev) (repair C ev) (prepared C ev entry))
      (layout.window.old.trans layout.window.label)
      ((Nat.le_add_left _ _).trans (Nat.le_of_lt (x).bankFit)) layout.window.capacity.1 i
  have paid : failed_stage_charges (fresh (x).form.pricedArea (x).form.stockSource) (x).mem
      (v.menu.maximum*v.menu.copiesAt v.copyScale width) :=
    fun i => ⟨(x).funded site reads seed i,credit i⟩
  rw [v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted] at paid
  exact paid

attribute [local irreducible] neighborhood

def purchased_failed_packets (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ))))
    (scheduled : Event.attempt ev∈events v.mesh)
    (failed : AttemptGate.actual (repair C ev).policy (postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry))=2)
    (many : v.loss*(2^z:ℕ) ≤ (T).selected.card)
    (stock : ∀ i : Commodity (Fin (2^z)) N₀ k, ((A).read (Succession v.mesh (.attempt ev)).1 entry).bits i ≤ v.keepLimit*width)
    (rateRoom : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width < 2^W) :
    v.failed_packet_account P z width r banks src tab dst owners ev entry time :=
  let spending := v.failed_packet_spending P z width r banks src tab dst owners ev entry layout run π scheduled stock rateRoom
    (v.purchased_failed_charges P z width r banks src tab dst owners phase trial slice inner entry fitted layout placed)
  v.failed_packet_of_bounds P z width r banks src tab dst owners ev entry layout run π time (x).nominal hw
    scheduled failed spending.1 spending.2 many
    (v.purchased_selected_bounds P z width r banks src tab dst owners phase trial slice inner entry fitted layout run
      time timeMin hw large letterFit base table resident placed words)

end Purchased
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
