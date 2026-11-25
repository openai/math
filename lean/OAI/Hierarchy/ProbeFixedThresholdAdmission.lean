import OAI.Hierarchy.ProbeFixedAffirmativeRows
import OAI.Hierarchy.ProbeFixedRawFunding
import OAI.Hierarchy.ProbeFixedFundingShape
import OAI.Hierarchy.ProbeFixedNativeStrips
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbeFixedRowTiles

namespace OAI
/-! # Every true high-score row of the physical two-branch audit can pay its debit -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open CatalystArchive PurchaseStage PurchaseFrozen PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "Goods" => Commodity (Fin (2^z)) N k
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "bs" => v.nativeBoards P z width
local notation "s[" t "]" => publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) t width v.precision

section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "J" => PayloadStrip.Quotes N k
local notation "surface" => (bs).outer phase trial
local notation "old" => ({(surface).old with base:=(f ev).market.shelf.stockBase})
local notation "pre" => (guard C ev).apply entry
local notation "B" => repair C ev
local notation "checked" => postSnapshot ((C).layout ev) B (prepared C ev entry)
local notation "t" => Calendar.time v.mesh v.finish ev
local notation "test" => v.payloadTest P z width phase trial
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "cells[" m "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z N k).stride
local notation "menu" => payloadMenu F N k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

include fitted in
omit [Nonempty (Fin k)] in
theorem payload_eligible (date : (v.finish:ℝ)/2≤t) (large : v.widthFloor≤width) (hw : 0<width)
    (late : v.stripHeight≤z) (initial : (H).Resident pre) («public» : (H).Resident checked) (maxWord : (H).payload.maxWord<2^W)
    (first : cells[pre]) (second : cells[checked])
    (row : Fin (f ev).market.rows) (h : row.val<(f ev).market.failures.rows)
    (high : (f ev).market.failures.cut<(f ev).market.failures.value pre ⟨row.val,h⟩) :
    (B).batch.packet.eval checked (row.val:Word W)≠0 ∧ ∀p,
      (((B).batch.need p).eval checked (row.val:Word W)).val≤(((B).batch.stock p).eval checked (row.val:Word W)).val := by
  have ht : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le date
  have above : (test).failure.cut<(test).failure.value pre row:=high
  have active : (f ev).market.failures.live.eval pre (row.val:Word W)≠0 := by
    intro asleep
    have zero : (test).failure.value pre row=0 := by
      change (test).failure.live.eval pre (row.val:Word W)=0 at asleep
      simp [FailureWords.value,FailureWords.effective,Expr.eval,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test,asleep]
    omega
  have original:=v.payload_live_lt P z width phase trial pre row (row.isLt.trans_le (v.market_rows_fit P z width late ev)) active
  let root:Fin (2^z):=⟨row.val,original⟩
  let hits:J→Goods:=PayloadStrip.rowAddress root
  have address (i : J) : ((x).addr i).eval checked (row.val:Word W)=(PurchaseInventory.slot (hits i):Word W) :=
    payloadSlot_read checked root i
  have read:=v.payload_packet_read P z width r banks src tab dst owners phase trial entry t ht row original pre checked initial «public» maxWord first second above
  have legal:=v.payload_key_legal P z width bills ev t ht entry root
  have model:=v.payload_row_funding (fixed_stage_count z v.W) t date
  obtain ⟨failed,recommendation⟩:=read
  obtain ⟨⟨inject,widths⟩,margin,rate⟩:=model
  let key:=v.rowKey P z width bills ev t ht entry hits
  let grid:=payloadGrid v.digitRadix v.precision key
  let lane (i : J):=(hits i).elim (fun _=>0) (fun _=>1)
  have copies : (x).board.copies=v.menu.copiesAt v.copyScale width := (v.catalogue_words (v.seed P z width) width).2.2
  have aPositive : 0 < (s[t]).a := by
    change 0 < (v.a : ℝ)
    exact_mod_cast v.quadratic_pos
  exact (x).affirmative_funded v.menu.width inject widths (s[t]) v.copyScale v.menu.margin lane
    aPositive ht (fun i=>by change 0 ≤ if i=0 then 0 else _;split <;> positivity)
    (Nat.cast_nonneg _) hw v.clock.base_pos (v.copied_widths width large).1 v.menu.margin_pos.le margin rate
    copies checked (row.val:Word W) grid legal failed recommendation.1
    (v.rowKey_lower_stock P z width bills ev t ht entry checked hits (surface).price (GlobalTests.offsets (surface).globalTests)
      old _ second (x).addr (row.val:Word W) address)

end

section
set_option maxRecDepth 4096
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "J" => ChainStrip.Axes v.depth k
local notation "surface" => (bs).inner phase trial slice inner
local notation "old" => ({(surface).old with base:=(f ev).market.shelf.stockBase})
local notation "pre" => (guard C ev).apply entry
local notation "B" => repair C ev
local notation "checked" => postSnapshot ((C).layout ev) B (prepared C ev entry)
local notation "t" => Calendar.time v.mesh v.finish ev
local notation "test" => v.purchasedTest P z width phase trial slice inner
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "cells[" m "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z N k).stride
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

include fitted in
omit [Nonempty (Fin k)] in
theorem purchased_eligible (date : (v.finish:ℝ)/2≤t) (large : v.widthFloor≤width) (hw : 0<width)
    (late : v.stripHeight≤z) (initial : (H).Resident pre) («public» : (H).Resident checked) (maxWord : (H).bought.maxWord<2^W)
    (first : cells[pre]) (second : cells[checked])
    (perm : Equiv.Perm (Fin (2^z))) (oldHeader : (h₀).Loaded pre) (nextHeader : (h₀).Loaded checked)
    (oldTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S perm v.depth key) pre)
    (nextTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S perm v.depth key) checked)
    (certify : ∀ j : Fin (f ev).market.rows, (f ev).market.failures.live.eval pre (j.val : Word W) ≠ 0 →
      v.PurchasedLiveRow P z width phase trial slice inner perm j)
    (row : Fin (f ev).market.rows) (h : row.val<(f ev).market.failures.rows)
    (high : (f ev).market.failures.cut<(f ev).market.failures.value pre ⟨row.val,h⟩) :
    (B).batch.packet.eval checked (row.val:Word W)≠0 ∧ ∀p,
      (((B).batch.need p).eval checked (row.val:Word W)).val≤(((B).batch.stock p).eval checked (row.val:Word W)).val := by
  have ht : 0<t := (half_pos (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos)).trans_le date
  have above : (test).failure.cut<(test).failure.value pre row:=high
  have active : (f ev).market.failures.live.eval pre (row.val : Word W) ≠ 0 := by
    intro asleep
    have zero : (test).failure.value pre row = 0 := by
      change (test).failure.live.eval pre (row.val : Word W) = 0 at asleep
      simp [FailureWords.value, FailureWords.effective, Expr.eval,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test, asleep]
    omega
  have rooms:=v.purchased_table_room z late
  obtain ⟨hits,signed,atFirst,address⟩:=v.purchased_raw_slots P z width phase trial slice inner perm pre checked
    oldHeader nextHeader oldTiles nextTiles rooms.1 rooms.2.1 row (certify row active)
  have read:=v.purchased_packet_read P z width r banks src tab dst owners phase trial slice inner entry t ht row hits pre checked initial «public» maxWord first second atFirst address signed above
  have legal:=v.purchased_key_legal P z width bills ev t ht entry hits signed
  have model:=v.purchased_row_funding t date
  obtain ⟨failed,recommendation⟩:=read
  obtain ⟨⟨inject,widths⟩,margin,rate⟩:=model
  let key:=v.rowKey P z width bills ev t ht entry hits
  let grid:=gridAxes v.digitRadix v.precision key
  let lane (i : J):=(hits i).elim (fun _=>0) (fun _=>1)
  have copies : (x).board.copies=v.menu.copiesAt v.copyScale width := (v.catalogue_words (v.seed P z width) width).2.2
  have aPositive : 0 < (s[t]).a := by
    change 0 < (v.a : ℝ)
    exact_mod_cast v.quadratic_pos
  exact (x).affirmative_funded v.menu.width inject widths (s[t]) v.copyScale v.menu.margin lane
    aPositive ht (fun i=>by change 0 ≤ if i=0 then 0 else _;split <;> positivity)
    (Nat.cast_nonneg _) hw v.clock.base_pos (v.copied_widths width large).1 v.menu.margin_pos.le margin rate
    copies checked (row.val:Word W) grid legal failed recommendation.1
    (v.rowKey_lower_stock P z width bills ev t ht entry checked hits (surface).price (GlobalTests.offsets (surface).globalTests)
      old _ second (x).addr (row.val:Word W) address)

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
