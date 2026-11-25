import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProtocolRAMDateSpillBilled

namespace OAI
/-! # The complete original dated paid list funds every occurrence of its spill -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT WireTelescope
open scoped Classical BigOperators Fin.CommRing

private theorem relabel {I E : Type*} [Fintype I] [DecidableEq E] {n : ℕ} (ι : I≃Fin n)
    (walk : I→List E) (quantity : Fin n→ℕ) (e : E) :
    routeLoad walk (fun i=>quantity (ι i)) e=
      routeLoad (fun j=>walk (ι.symm j)) quantity e := by
  let cost:=fun j=>(walk (ι.symm j)).count e*quantity j
  simpa only [routeLoad,cost,Equiv.symm_apply_apply] using ι.sum_comp cost

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "stageCount" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "cells" => PurchaseInventory.footprint h stageCount k
local notation "rows" => (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "fmt" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width)
    v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "ord" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "feeds" => FeedLayout.atEvent (N:=stageCount) v.mesh A fmt (P).joint.initial width v.keepLimit
local notation "oc" => v.catalystPairOwners P h width
local notation "pa" => v.catalystPairParity P h width
local notation "order" => v.wideOrder h width
local notation "dates" => events v.mesh
variable (bits size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π ord seed
local notation "mount" => (P).catalogue.coreMount π (siteNumber h D k) order chk
local notation "walk" => v.spillPath P h π order
local notation "compile" => v.wideEventSlices h width bits

def SpillPaidRoom : Prop :=
  Fintype.card (Actions stageCount k)≤2^w ∧ Fintype.card (Commodity (Fin (2^h)) stageCount k)≤2^w ∧
  (∀l : Fin (FeedLayout.lanes stageCount k),laneWidth (decodeLane l)*2^h<2^w) ∧
  (∀t,(v.widePlacement h t).catalogue.rows<2^w) ∧ v.wideStockHeight≤h

private theorem eventually_spill_paid_room : ∀ᶠ h : ℕ in Filter.atTop,v.SpillPaidRoom h := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h hs boards age
  exact ⟨hs.1,hs.2.1,hs.2.2,fun t=>(boards t).1,age⟩

def wideSpillPaidHeight := Nat.find (Filter.eventually_atTop.1 v.eventually_spill_paid_room)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option cleanup.letToHave false in
/-- At each actual date the commodity rank page can use the original retained
cash snapshot. The repair list contains the whole core spill, and the feed list
is the sum of exactly its ordinary and signed stock lanes. -/
theorem wide_spill_event_le (first : ℕ) (j : Fin (dates).length) (before : Memory w)
    (age : v.wideSpillPaidHeight≤h) (extent : (A).endAddress v.mesh≤ size)
    (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (low : ∀a,a<(A).endAddress v.mesh→before a=chk a) (e : Fin rows) :
    routeLoad (mount).ordinary (fun i=>RouteSettlement.actual
      (v.wideSpillPage h width bits first j.val).overflow before (PurchaseInventory.slot i)) e≤
        PaidWidths.total (compile ((dates).get j)) chk e := by
  have rooms:=(Nat.find_spec (Filter.eventually_atTop.1 v.eventually_spill_paid_room)) h age
  obtain ⟨menu,goods,lanes,boards,stockAge⟩:=rooms
  have scalar : cells≤2^w := by simpa only [PurchaseInventory.card_commodity] using goods
  have heap:=(v.wide_stock_sizes h width stockAge budget small).words.addresses
  have funded:=v.wide_stock_at h width size extent v.radius π seed stockAge budget small
  obtain ⟨seen,rom⟩:=(v.wide_spill_source h width size extent π seed heap funded.mounted_all).2
  have edges:=(boards width).le
  rw [v.wide_spill_overflow h width bits first j]
  have present:=(dates).get_mem j
  cases event : (dates).get j with
  | attempt a =>
    let ar:=(fmt a).pricedArea
    let t:=v.paidSpillPath P h width recipe route ord a
    let slots:=v.nativeSlots P h width a
    let value:=fun j : Fin ar.goods=>(chk (ar.output+ar.goods+ar.goods+j.val)).val
    have read:=v.spill_read P h width π order chk route seen recipe _ rom menu goods edges oc pa a
    have price:=t.spill_load ar chk e (fun i=>walk (slots.symm i)) read
    have live : Event.attempt a∈dates := event ▸ present
    have upto:=(A).within v.mesh (.attempt a) live
    have space:=v.attempt_room P h width a
    change ar.output+3*ar.goods≤(A).base v.mesh (.attempt a)+(A).stride at space
    have scalarAt (i : Commodity (Fin (2^h)) stageCount k) : RouteSettlement.actual
        (ProtocolRAMDateSpillRank.attemptBank h stageCount k ar) before (PurchaseInventory.slot i)=value (slots i) := by
      rw [ProtocolRAMDateSpillRank.attempt_read ar before i scalar]
      have inside : PurchaseInventory.slot i<ar.goods := by
        change PurchaseInventory.slot i<(fmt a).pricedArea.goods
        rw [v.stock_goods P h width a]
        exact PurchaseInventory.slot_lt i
      have below : ar.output+2*ar.goods+PurchaseInventory.slot i < (A).endAddress v.mesh := calc
        _ < ar.output+2*ar.goods+ar.goods := Nat.add_lt_add_left inside _
        _ = ar.output+3*ar.goods := by omega
        _ ≤ _ := space.trans upto
      rw [low _ below]
      change (chk (ar.output+2*ar.goods+PurchaseInventory.slot i)).val=
        (chk (ar.output+ar.goods+ar.goods+(slots i).val)).val
      rw [show (slots i).val=PurchaseInventory.slot i from v.slot_index P h width a i]
      rw [show ar.output+2*ar.goods+PurchaseInventory.slot i=ar.output+ar.goods+ar.goods+PurchaseInventory.slot i by omega]
    let slice:=PaidWidths.paidSpill ar t.positions t.owner t.parity t.edge t.sourceRow
    have member : slice∈compile (.attempt a) := by
      change slice∈(fmt a).paidSlices _ _ _ _ _ t bits
      simp [Format.paidSlices,slice,ar]
    calc
      _ = routeLoad walk (fun i=>value (slots i)) e :=
        congrArg (fun q=>routeLoad walk q e) (funext scalarAt)
      _ = routeLoad (fun i=>walk (slots.symm i)) value e := relabel slots walk value e
      _ = slice.load chk e := price.symm
      _ ≤ _ := List.le_sum_of_mem (List.mem_map.mpr ⟨slice,member,rfl⟩)
  | feed b =>
    let L:=feeds b
    let t:=v.paidFeedPath P h width route feeds b
    let slots:=PurchaseInventory.slotEquiv h stageCount k
    let value:=fun i : Fin cells=>(chk (L.overflow+i.val)).val
    have read (l : Fin (FeedLayout.lanes stageCount k)) :=
      v.boundary_read P h π order chk route seen L oc pa l (lanes l) edges
    have price:=L.installed_load t chk e (fun i=>walk (slots.symm i)) read
    have live : Event.feed b∈dates := event ▸ present
    have upto:=(A).within v.mesh (.feed b) live
    have space:=v.feed_room P h width
    have scalarAt (i : Commodity (Fin (2^h)) stageCount k) :
        RouteSettlement.actual (ProtocolRAMDateSpillRank.feedBank L) before (PurchaseInventory.slot i)=
          value (slots i) := by
      change RouteSettlement.actual (ProtocolRAMDateSpillRank.amountBank h stageCount k L.overflow) before _=_
      rw [ProtocolRAMDateSpillRank.amountBank_read _ before i scalar]
      have startEq : L.overflow=(A).base v.mesh (.feed b)+cells := rfl
      have below : L.overflow+PurchaseInventory.slot i < (A).endAddress v.mesh := calc
        _ < L.overflow+cells := Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _
        _ = (A).base v.mesh (.feed b)+2*cells := by rw [startEq,Nat.add_assoc,two_mul]
        _ ≤ _ := (Nat.add_le_add_left space _).trans upto
      exact congrArg (fun word : Word w=>word.val) (low _ below)
    calc
      _ = routeLoad walk (fun i=>value (slots i)) e :=
        congrArg (fun q=>routeLoad walk q e) (funext scalarAt)
      _ = routeLoad (fun i=>walk (slots.symm i)) value e := relabel slots walk value e
      _ ≤ _ := price.symm.le

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
