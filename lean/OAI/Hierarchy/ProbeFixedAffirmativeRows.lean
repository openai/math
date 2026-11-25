import OAI.Hierarchy.ProbeFixedRowPages
import OAI.Hierarchy.ProbeCommittedMenuRead

namespace OAI
/-! # An affirmative score reads a genuine positive packet and its histogram arity -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "stageCount" => Stages z (2^v.W)
local notation "Goods" => Commodity (Fin (2^z)) stageCount k
local notation "H" => v.publicHeader P z width
local notation "bs" => v.nativeBoards P z width
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "fm" => v.nativeFormats P z width
local notation "s[" t "]" => publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) t width v.precision
local instance affirmativeRowsPayloadRoleNonempty : Nonempty (PayloadRole stageCount k) := ⟨.catalyst (PayloadStrip.first stageCount 0) ⟨0,v.positive⟩⟩
local instance affirmativeRowsPurchasedRoleNonempty : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩

section
variable (phase trial : ℕ)
local notation "ev" => Attempt.outer phase trial
local notation "u₀" => DeadlineROM.index v.mesh ev
local notation "surface" => (bs).outer phase trial
local notation "channels" => (payloadChannels z stageCount k)
local notation "old" => ({(surface).old with base:=(fm ev).market.shelf.stockBase})
local notation "J" => PayloadStrip.Quotes stageCount k
local notation "menu" => payloadMenu F stageCount k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
local notation "test" => v.payloadTest P z width phase trial
local notation "grid₀" => v.payloadPagePrice z width
variable (entry : Memory (wordBits z (2^v.W) copies)) (t : ℝ) (ht : 0<t)
    (j : Fin (v.payloadTest P z width phase trial).rows) (original : j.val<2^z)
local notation "hits" => (PayloadStrip.rowAddress (N:=stageCount) (k:=k) (⟨j.val,original⟩ : Fin (2^z)))
local notation "key" => v.rowKey P z width bills ev t ht entry hits
local notation "slotRead[" m "]" => (∀ i : J,((channels).address i).eval m (j.val:Word W)=(PurchaseInventory.slot (hits i):Word W))
local notation "cells[" m "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z stageCount k).stride

theorem payloadKey_read (state : Memory W) (stored : cells[state])  :
    ∀ h,((test).quoted h).eval state (j.val:Word W)=((key h).val:Word W) := by
  have read (i : J) :
      ((channels).digit ((Fintype.equivFin J) i)).eval state (j.val:Word W) =
        (PurchaseInventory.slot (hits i):Word W) := by
    dsimp only [Channels.digit]
    rw [Equiv.symm_apply_apply]
    exact payloadSlot_read state (⟨j.val,original⟩ : Fin (2^z)) i
  exact v.rowKey_read P z width bills ev t ht entry state hits (surface).price (GlobalTests.offsets (surface).globalTests)
    old _ stored (channels).digit (j.val:Word W) read

theorem payload_packet_read (pre state : Memory W)
    (initial : (H).Resident pre) («public» : (H).Resident state) (room : (H).payload.maxWord<2^W)
    (first : cells[pre]) (second : cells[state])
    (high : (test).failure.cut<(test).failure.value pre j) :
    let grid:=PayloadStrip.prices stageCount k v.radius (payloadGrid v.digitRadix v.precision key)
    let legal:=v.payload_key_legal P z width bills ev t ht entry (⟨j.val,original⟩ : Fin (2^z))
    ∃ h : (bs).tolerance≤Probe.discrepancy F (PayloadStrip.wires stageCount k) (PayloadStrip.demands stageCount k) grid,
      let i:=(menu).select ⟨grid,legal,h⟩
      (b ev).packet.eval state (j.val:Word W)=(((Fintype.equivFin (menu).index i).val+1:ℕ):Word W) ∧
      (b ev).termCount.read state ((b ev).packet.eval state (j.val:Word W))=(((menu).packet i).terms:Word W) := by
  intro grid legal
  have paged : grid₀ u₀ key=grid := v.payload_page_grid z width u₀ key
  have port:=v.payload_page_operands P z width r banks src tab dst owners phase trial
  have pub:=v.payload_page_read P z width phase trial state «public»
  have vec:=v.payload_vector P z width phase trial pre initial room key
  have atStart:=v.payloadKey_read P z width r banks src tab dst owners phase trial entry t ht j original pre first
  have atEnd:=v.payloadKey_read P z width r banks src tab dst owners phase trial entry t ht j original state second
  have good : grid₀ u₀ key ∈ (PayloadStrip.prices stageCount k v.radius) ''
      Set.Icc 0 (PayloadStrip.ceiling stageCount k v.radius) := by
    rw [paged]
    exact legal
  have run:=MenuROM.selected_packet menu test (H).bought.stop (H).menus.right.stop grid₀ u₀ (b ev) pre state j key
    rfl (bs).tolerance_pos.le v.clock.precision_pos high atStart vec.1 vec.2 good
    port.1 port.2.1 port.2.2.1 port.2.2.2 pub.1 pub.2 atEnd
  obtain ⟨qualified,packet,arity⟩:=run
  have eligible : (bs).tolerance ≤ Probe.discrepancy F
      (PayloadStrip.wires stageCount k) (PayloadStrip.demands stageCount k) grid := by
    rw [←paged]
    exact qualified
  have selected : (menu).select ⟨grid₀ u₀ key,good,qualified⟩ = (menu).select ⟨grid,legal,eligible⟩ :=
    congrArg (menu).select (Subtype.ext paged)
  refine ⟨eligible,?_,?_⟩
  · exact packet.trans (congrArg (fun i : (menu).index =>
      (((Fintype.equivFin (menu).index i).val+1:ℕ):Word W)) selected)
  · exact arity.trans (congrArg (fun i : (menu).index => (((menu).packet i).terms:Word W)) selected)

end
section
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "u₀" => DeadlineROM.index v.mesh ev
local notation "surface" => (bs).inner phase trial slice inner
local notation "channels" => (purchasedChannels (z:=z) (d:=2^v.W) (k:=k) ((bs).outer phase trial).market.shelf (bs).sampler v.depth ((bs).stratumHeader phase trial))
local notation "old" => ({(surface).old with base:=(fm ev).market.shelf.stockBase})
local notation "J" => ChainStrip.Axes v.depth k
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "grid₀" => v.purchasedPagePrice width
variable (entry : Memory (wordBits z (2^v.W) copies)) (t : ℝ) (ht : 0<t)
    (j : Fin (v.purchasedTest P z width phase trial slice inner).rows)
    (hits : ChainStrip.Axes v.depth k → Commodity (Fin (2^z)) (Stages z (2^v.W)) k)
local notation "key" => v.rowKey P z width bills ev t ht entry hits
local notation "slotRead[" m "]" => (∀ i : J,((channels).address i).eval m (j.val:Word W)=(PurchaseInventory.slot (hits i):Word W))
local notation "cells[" m "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z stageCount k).stride

theorem purchasedKey_read (state : Memory W) (stored : cells[state]) (slots : slotRead[state]) :
    ∀ h,((test).quoted h).eval state (j.val:Word W)=((key h).val:Word W) := by
  have read (i : J) :
      ((channels).digit ((Fintype.equivFin J) i)).eval state (j.val:Word W) =
        (PurchaseInventory.slot (hits i):Word W) := by
    dsimp only [Channels.digit]
    rw [Equiv.symm_apply_apply]
    exact slots i
  exact v.rowKey_read P z width bills ev t ht entry state hits (surface).price (GlobalTests.offsets (surface).globalTests)
    old _ stored (channels).digit (j.val:Word W) read

theorem purchased_packet_read (pre state : Memory W)
    (initial : (H).Resident pre) («public» : (H).Resident state) (room : (H).bought.maxWord<2^W)
    (first : cells[pre]) (second : cells[state])
    (before : slotRead[pre]) (after : slotRead[state]) (signed : ∀i,(hits i).elim (fun _=>0) (fun _=>1)=1)
    (high : (test).failure.cut<(test).failure.value pre j) :
    let grid:=ChainStrip.prices v.depth k v.radius (gridAxes v.digitRadix v.precision key)
    let legal:=v.purchased_key_legal P z width bills ev t ht entry hits signed
    ∃ h : (bs).tolerance≤Probe.discrepancy F (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) grid,
      let i:=(menu).select ⟨grid,legal,h⟩
      (b ev).packet.eval state (j.val:Word W)=(((Fintype.equivFin (menu).index i).val+1:ℕ):Word W) ∧
      (b ev).termCount.read state ((b ev).packet.eval state (j.val:Word W))=(((menu).packet i).terms:Word W) := by
  intro grid legal
  have paged : grid₀ u₀ key=grid := v.purchased_page_grid width u₀ key
  have port:=v.purchased_page_operands P z width r banks src tab dst owners phase trial slice inner
  have pub:=v.purchased_page_read P z width phase trial slice inner state «public»
  have vec:=v.purchased_vector P z width phase trial slice inner pre initial room key
  have atStart:=v.purchasedKey_read P z width r banks src tab dst owners phase trial slice inner entry t ht j hits pre first before
  have atEnd:=v.purchasedKey_read P z width r banks src tab dst owners phase trial slice inner entry t ht j hits state second after
  have good : grid₀ u₀ key ∈ (ChainStrip.prices v.depth k v.radius) ''
      Set.Icc 0 (fun _=>v.radius+1) := by
    rw [paged]
    exact legal
  have run:=MenuROM.selected_packet menu test (H).menus.left.stop (H).menus.leftAlphabet.stop grid₀ u₀ (b ev) pre state j key
    rfl (bs).tolerance_pos.le v.clock.precision_pos high atStart vec.1 vec.2 good
    port.1 port.2.1 port.2.2.1 port.2.2.2 pub.1 pub.2 atEnd
  obtain ⟨qualified,packet,arity⟩:=run
  have eligible : (bs).tolerance ≤ Probe.discrepancy F
      (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) grid := by
    rw [←paged]
    exact qualified
  have selected : (menu).select ⟨grid₀ u₀ key,good,qualified⟩ = (menu).select ⟨grid,legal,eligible⟩ :=
    congrArg (menu).select (Subtype.ext paged)
  refine ⟨eligible,?_,?_⟩
  · exact packet.trans (congrArg (fun i : (menu).index =>
      (((Fintype.equivFin (menu).index i).val+1:ℕ):Word W)) selected)
  · exact arity.trans (congrArg (fun i : (menu).index => (((menu).packet i).terms:Word W)) selected)

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
