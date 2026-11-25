import OAI.Hierarchy.ProbeFixedRowEconomy
import OAI.Hierarchy.ProbeFixedMountedRates
import OAI.Hierarchy.ProbeFixedNativeStrips
import OAI.Hierarchy.ProbeFixedFailureEconomy

namespace OAI
/-! # Positive widths, finite quote gains and curvature on the two actual posted tapes -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory CoreBoard
open scoped BigOperators Classical
attribute [local irreducible] permutationFabric
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

/-- The three successive local requirements in `failed_packets`, on its exact
native chart and the exact finite original-coordinate layout. -/
def SelectedBounds (a : Attempt) (entry : Memory W)
    (L : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (run : ready C (.attempt a) entry)
    (π : PortPlan (st a) (b a) (input a entry) (f a).market.rows) (time : ℝ) (nominal : Fin (f a).market.rows → ℕ) : Prop :=
  let T:=v.selectedTape P z width r banks src tab dst owners a entry L run π
  let B:=(A).bank.coordinates (v.nativeSlots P z width a)
  let p:=activePrice T.kind T.weight (maximizer B.a B.M time B.coefficient B.box
    (B.units width ((A).read (Succession v.mesh (.attempt a)).1 entry)))
  (∀ j∈T.selected,0<nominal j ∧ 2*(v.actualK*nominal j)≤width) ∧
    (∀ j∈T.selected,
      (∑e,(T.put (π.enum ⟨j,e⟩):ℝ)*p (π.enum ⟨j,e⟩))+T.broadcast j+
        (copied v.actualK (nominal j) width:ℝ)*(nominal j*v.menu.margin/2) ≤
        ∑e,(T.take (π.enum ⟨j,e⟩):ℝ)*p (π.enum ⟨j,e⟩)) ∧
    (∑i,(stockChange T.kind (netUnits width T.put T.take) i)^2/(4*time*B.a)) ≤
      (2^z:ℕ)*v.loss*v.menu.margin/(8*v.actualK)


private theorem selected_filter_degree {E : Type*} (pred : E → Prop)
    {sourceEnum targetEnum : Fintype E} {sourceDec targetDec : DecidablePred pred}
    (bound : (@Finset.filter E pred sourceDec (@Finset.univ E sourceEnum)).card ≤ 1) :
    (@Finset.filter E pred targetDec (@Finset.univ E targetEnum)).card ≤ 1 := by
  cases Subsingleton.elim sourceEnum targetEnum
  cases Subsingleton.elim sourceDec targetDec
  exact bound

omit [Nonempty (Fin k)] in
private theorem selected_commodity_count (a : Attempt) :
    (Fintype.card (Fin (st a).goods) : ℝ) ≤ ((1+2*publicStages v.W*k : ℕ) : ℝ)*(2^z : ℕ) := by
  have goods : (st a).goods = PurchaseInventory.footprint z N₀ k := v.stock_goods P z width a
  have footprint : PurchaseInventory.footprint z N₀ k = (1+2*publicStages v.W*k)*2^z := by
    unfold PurchaseInventory.footprint
    rw [show N₀=publicStages v.W from fixed_stage_count z v.W]
    ring
  have cardinal := (Fintype.card_fin (st a).goods).trans (goods.trans footprint)
  rw [cardinal,Nat.cast_mul]

omit [Nonempty (Fin k)] in
private theorem selected_tape_curvature (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time)
    (I : Type) [Fintype I] (rows edges n width : ℕ) (t : SelectedRows.Tape rows edges I)
    (positive : 0<width) (count : (Fintype.card I:ℝ)≤(1+2*publicStages v.W*k:ℕ)*n)
    (degree : ∀i,(Finset.univ.filter (fun e=>t.activeKind e=some i)).card≤1)
    {J : Type*} (localRate : J → ℕ)
    (movement : ∀e,∃j : J,v.copyScale*(t.put (t.use e)+t.take (t.use e))≤width*localRate j)
    (renamed : ∀j,∃m : v.payloadPackets.index ⊕ v.boughtPackets.index,localRate j=v.menu.rate m) :
    (∑i,(stockChange t.kind (netUnits width t.put t.take) i)^2/(4*time*(v.a:ℝ)))≤
      (n:ℝ)*v.loss*v.menu.margin/(8*(v.actualK:ℝ)) :=
  v.clock.rate time timeMin I rows edges n width t positive count degree (fun e => by
    obtain ⟨j,small⟩ := movement e
    obtain ⟨m,reindex⟩ := renamed j
    exact ⟨m,small.trans_eq (congrArg (fun rate : ℕ => width*rate) reindex)⟩)


section Payload
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
include run in
omit [Nonempty (Fin k)] in
private theorem payload_row_mounted :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem
  rw [v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted]
  exact v.entered P z width r banks src tab dst owners ev entry run

local notation "mount" => v.payload_row_mounted P z width r banks src tab dst owners phase trial entry fitted run
include layout in
omit [Nonempty (Fin k)] in
private theorem payload_row_broadcast :
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted]
  exact fresh_broadcastRoom (f ev).pricedArea (f ev).stockSource (b ev) layout.inputs layout.window.room

local notation "bc" => v.payload_row_broadcast P z width r banks src tab dst owners phase trial entry fitted layout
local notation "links" => v.printedCharge P z width ev
local notation "treeCost" => (fun (_ : Fin (f ev).market.rows) (_ : ℕ) => v.cost.atAttempt ev)
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout run π
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "bs" => v.nativeBoards P z width
local notation "menu" => payloadMenu F N₀ k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

omit [Nonempty (Fin k)] in
private theorem payload_live_row (j : Fin (f ev).market.rows) :
    j ∈ (T).selected ↔ j ∈ liveRows (x).ballot (x).mem (f ev).market.rows := by
  change j ∈ liveRows (b ev) (input ev entry) (f ev).market.rows ↔ _
  rw [v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted]

attribute [local irreducible] neighborhood

set_option maxHeartbeats 2400000 in
private abbrev payload_row_estimates (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :=
  let rates := v.mounted_payload (fixed_stage_count z v.W) width large
  let numeric := v.catalogue_words (v.seed P z width) width
  have letterEq : ((StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet)=v.menu.alphabet :=
    numeric.1
  have peak : (x).ballot.maxWidth=v.menu.maximum := numeric.2.1
  have copies : (x).ballot.copies=v.menu.copiesAt v.copyScale width := numeric.2.2
  let bound (i : (menu).index) := rates.2 i
  have ordinals (i : (menu).index) :
      ((menu).packet i).terms ≤ (StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet ∧
        ((menu).packet i).terms < 2^W := ⟨(bound i).1.trans_eq letterEq.symm,(bound i).1.trans_lt letterFit⟩
  let estimates := (x).row_economy mount bc (keys ev) links treeCost placed price[time] v.menu.margin (1/(v.precision:ℝ))
    v.copyScale v.actualK width base v.menu.margin_pos.le rates.1 (by positivity) (v.cost.nonneg ev)
    ordinals table resident (fun _ _ => le_rfl)
    (fun i => (congrArg (fun n : ℕ => (Fintype.card (PayloadRole N₀ k):ℝ)*n*(1/(v.precision:ℝ))) peak).le.trans
      (bound i).2.1)
    (fun i => ⟨(bound i).2.2.1.trans_eq copies.symm,copies.le.trans (bound i).2.2.2.1⟩)
    (fun j hj => words j ((v.payload_live_row P z width r banks src tab dst owners phase trial entry fitted layout run j).2 hj))
  let sourceTape := (fresh (x).form.pricedArea (x).form.stockSource).tape (x).ballot (x).mem
    (x).plan mount bc (keys ev) links treeCost
  let curvature := v.selected_tape_curvature time timeMin (Fin (x).raw.coordinates)
    (x).raw.market.rows (fresh (x).form.pricedArea (x).form.stockSource).occurrences
    (2^z) width sourceTape hw (v.selected_commodity_count P z width ev)
    (fun i => selected_filter_degree (fun e => sourceTape.activeKind e = some i) (estimates.2.1 i))
    (fun i : (menu).index => packetRate ((menu).packet i)) estimates.2.2
    (fun i => (bound i).2.2.2.2.1)
  And.intro estimates.1 curvature

set_option maxHeartbeats 2400000 in
omit [Nonempty (Fin k)] in
private theorem payload_row_sizes (time : ℝ) (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :
    ∀ j ∈ (T).selected, 0<(x).nominal j ∧ 2*(v.actualK*(x).nominal j)≤width := by
  have rates := v.mounted_payload (fixed_stage_count z v.W) width large
  have bound (i : (menu).index) := rates.2 i
  intro j live
  obtain ⟨record⟩ := words j live
  obtain ⟨h,recommended⟩ := record.recommendation
  let i := (menu).select ⟨_,record.inside,h⟩
  have code := ((x).decoded_packet_words j i ((bound i).1.trans_lt letterFit) recommended).1
  exact (congrArg (fun n : ℕ => 0<n ∧ 2*(v.actualK*n)≤width)
    ((x).nominal_code j i code)).mpr (bound i).2.2.2.2.2

set_option maxHeartbeats 2400000 in
omit [Nonempty (Fin k)] in
theorem payload_selected_bounds (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :
    v.SelectedBounds P z width r banks src tab dst owners ev entry layout run π time (x).nominal := by
  have hv := v.payload_row_estimates P z width r banks src tab dst owners phase trial entry fitted layout run
    time timeMin hw large letterFit base table resident placed words
  exact ⟨v.payload_row_sizes P z width r banks src tab dst owners phase trial entry fitted layout run
    time large letterFit words,hv.1,hv.2⟩

end Payload

section Purchased
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
include run in
omit [Nonempty (Fin k)] in
private theorem purchased_row_mounted :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem
  rw [v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted]
  exact v.entered P z width r banks src tab dst owners ev entry run

local notation "mount" => v.purchased_row_mounted P z width r banks src tab dst owners phase trial slice inner entry fitted run
include layout in
omit [Nonempty (Fin k)] in
private theorem purchased_row_broadcast :
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted]
  exact fresh_broadcastRoom (f ev).pricedArea (f ev).stockSource (b ev) layout.inputs layout.window.room

local notation "bc" => v.purchased_row_broadcast P z width r banks src tab dst owners phase trial slice inner entry fitted layout
local notation "links" => v.printedCharge P z width ev
local notation "treeCost" => (fun (_ : Fin (f ev).market.rows) (_ : ℕ) => v.cost.atAttempt ev)
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout run π
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "bs" => v.nativeBoards P z width
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

omit [Nonempty (Fin k)] in
private theorem purchased_live_row (j : Fin (f ev).market.rows) :
    j ∈ (T).selected ↔ j ∈ liveRows (x).ballot (x).mem (f ev).market.rows := by
  change j ∈ liveRows (b ev) (input ev entry) (f ev).market.rows ↔ _
  rw [v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted]

attribute [local irreducible] neighborhood

set_option maxHeartbeats 2400000 in
private abbrev purchased_row_estimates (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :=
  let rates := v.mounted_purchased width large
  let numeric := v.catalogue_words (v.seed P z width) width
  have letterEq : ((StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet)=v.menu.alphabet :=
    numeric.1
  have peak : (x).ballot.maxWidth=v.menu.maximum := numeric.2.1
  have copies : (x).ballot.copies=v.menu.copiesAt v.copyScale width := numeric.2.2
  let bound (i : (menu).index) := rates.2 i
  have ordinals (i : (menu).index) :
      ((menu).packet i).terms ≤ (StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet ∧
        ((menu).packet i).terms < 2^W := ⟨(bound i).1.trans_eq letterEq.symm,(bound i).1.trans_lt letterFit⟩
  let estimates := (x).row_economy mount bc (keys ev) links treeCost placed price[time] v.menu.margin (1/(v.precision:ℝ))
    v.copyScale v.actualK width base v.menu.margin_pos.le rates.1 (by positivity) (v.cost.nonneg ev)
    ordinals table resident (fun _ _ => le_rfl)
    (fun i => (congrArg (fun n : ℕ => (Fintype.card (PurchasedRole v.depth k):ℝ)*n*(1/(v.precision:ℝ))) peak).le.trans
      (bound i).2.1)
    (fun i => ⟨(bound i).2.2.1.trans_eq copies.symm,copies.le.trans (bound i).2.2.2.1⟩)
    (fun j hj => words j ((v.purchased_live_row P z width r banks src tab dst owners phase trial slice inner entry fitted layout run j).2 hj))
  let sourceTape := (fresh (x).form.pricedArea (x).form.stockSource).tape (x).ballot (x).mem
    (x).plan mount bc (keys ev) links treeCost
  let curvature := v.selected_tape_curvature time timeMin (Fin (x).raw.coordinates)
    (x).raw.market.rows (fresh (x).form.pricedArea (x).form.stockSource).occurrences
    (2^z) width sourceTape hw (v.selected_commodity_count P z width ev)
    (fun i => selected_filter_degree (fun e => sourceTape.activeKind e = some i) (estimates.2.1 i))
    (fun i : (menu).index => packetRate ((menu).packet i)) estimates.2.2
    (fun i => (bound i).2.2.2.2.1)
  And.intro estimates.1 curvature

set_option maxHeartbeats 2400000 in
omit [Nonempty (Fin k)] in
private theorem purchased_row_sizes (time : ℝ) (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :
    ∀ j ∈ (T).selected, 0<(x).nominal j ∧ 2*(v.actualK*(x).nominal j)≤width := by
  have rates := v.mounted_purchased width large
  have bound (i : (menu).index) := rates.2 i
  intro j live
  obtain ⟨record⟩ := words j live
  obtain ⟨h,recommended⟩ := record.recommendation
  let i := (menu).select ⟨_,record.inside,h⟩
  have code := ((x).decoded_packet_words j i ((bound i).1.trans_lt letterFit) recommended).1
  exact (congrArg (fun n : ℕ => 0<n ∧ 2*(v.actualK*n)≤width)
    ((x).nominal_code j i code)).mpr (bound i).2.2.2.2.2

set_option maxHeartbeats 2400000 in
omit [Nonempty (Fin k)] in
theorem purchased_selected_bounds (time : ℝ) (timeMin : (v.finish:ℝ)/2≤time) (hw : 0<width)
    (large : v.widthFloor≤width) (letterFit : v.menu.alphabet<2^W) (base : ℕ)
    (table : (st ev).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident (input ev entry))
    (placed : (x).Placed)
    (words : ∀ j : Fin (f ev).market.rows, j∈(T).selected →
      Nonempty ((x).RowRead mount bc (keys ev) links treeCost j price[time] (1/(v.precision:ℝ)))) :
    v.SelectedBounds P z width r banks src tab dst owners ev entry layout run π time (x).nominal := by
  have hv := v.purchased_row_estimates P z width r banks src tab dst owners phase trial slice inner entry fitted layout run
    time timeMin hw large letterFit base table resident placed words
  exact ⟨v.purchased_row_sizes P z width r banks src tab dst owners phase trial slice inner entry fitted layout run
    time large letterFit words,hv.1,hv.2⟩

end Purchased
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
