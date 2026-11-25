import OAI.Hierarchy.ProbeFixedWideSpillMiddle
import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProbeFixedPaidOverflowAtCheckout

namespace OAI
/-! # Bounding the original dated overflow on the signed counted execution -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "compile" => v.wideEventSlices h width bits
local notation "hi" => v.wideRoleStart h width stock ss
local notation "base" => (sizes).stop hi
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "source" => TerminalLayout.source page
local notation "table" => TerminalLayout.table page
local notation "target" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r rows
local notation "es" => events v.mesh
local notation "cells" => PurchaseInventory.footprint h N k
local notation "K" => Fintype.card (RoleProgram.Old h v.W k rows)

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "mount" => (P).catalogue.coreMount π (siteNumber h D k) order chk
local notation "value" => v.wideDatedValue h width bits mid chk

theorem wide_spill_page_floor (first : ℕ) (j : Fin last)
    (heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span cells≤first) :
    let region:=v.wideSpillPage h width bits first j.val
    region.overflow.base+region.overflow.size≤first := by
  intro region
  rw [show region.overflow=(v.wideSpillPage h width bits first j.val).overflow from rfl,
    v.wide_spill_overflow]
  have occ:=(events v.mesh).get_mem j
  cases code : (events v.mesh).get j with
  | attempt a=>
    let ar:=(v.nativeFormats P h width a).pricedArea
    have atDate : Event.attempt a∈events v.mesh:=code ▸ occ
    have span:=v.attempt_room P h width a
    change ar.output+3*ar.goods≤(A).base v.mesh (.attempt a)+(A).stride at span
    have endAt:=(A).within v.mesh _ atDate
    change ar.output+2*ar.goods+ProtocolRAMPurchaseSampler.span cells≤first
    omega
  | feed b=>
    have atDate : Event.feed b∈events v.mesh:=code ▸ occ
    have span:=v.feed_room P h width
    have endAt:=(A).within v.mesh _ atDate
    change (A).base v.mesh (.feed b)+cells+ProtocolRAMPurchaseSampler.span cells≤first
    omega

theorem wide_spill_page_below (first : ℕ) (j : Fin last)
    (heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span cells≤first) :
    let region:=v.wideSpillPage h width bits first j.val
    region.overflow.base+region.overflow.size≤region.rankStart := by
  intro region
  have lower : first≤region.floor:=by
    change first≤first+(v.wideSpillRanks h width bits first).zero.size+j.val*(v.wideSpillRanks h width bits first).stride
    omega
  exact (v.wide_spill_page_floor h width bits first j heap).trans (lower.trans (Nat.le_add_right ..))

noncomputable def wideSpillOverflowHeight : ℕ :=
  Nat.find (Filter.eventually_atTop.1 v.wide_paid_overflow_cells)

set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
theorem wide_spill_overflow_bound (startPage : ℕ) (j : Fin last) (before : Memory w)
    (age : v.wideSpillOverflowHeight≤h) (extent : (A).endAddress v.mesh≤ size)
    (floor : v.widthFloor≤width) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (scalar : cells≤2^w) (radius : M=v.radius) (bought : chk ((A).endAddress v.mesh)=0)
    (low : ∀a<(A).endAddress v.mesh,before a=chk a) (x : Goods h v.W k) :
    RouteSettlement.actual (v.wideSpillPage h width bits startPage j.val).overflow before (PurchaseInventory.slot x)
      ≤ max v.menu.maximum (v.keepLimit+1)*width := by
  let checkout := v.wideSignedCheckoutAt h width size stock v.radius π o seed
  have checkout_eq : chk = checkout :=
    congrArg (fun t => v.wideSignedCheckoutAt h width size stock t π o seed) radius
  have accepted : checkout ((A).endAddress v.mesh) = 0 :=
    (congrFun checkout_eq _).symm.trans bought
  have native:=(Nat.find_spec (Filter.eventually_atTop.1 v.wide_paid_overflow_cells)) h age
    width small floor budget size extent π seed accepted
  let f:=v.nativeFormats P h width
  let feeds:=FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit
  have occ:=(events v.mesh).get_mem j
  have slot:=PurchaseInventory.slot_lt x
  rw [v.wide_spill_overflow h width bits startPage j]
  cases event : (events v.mesh).get j with
  | attempt a=>
    let ar:=(f a).pricedArea
    have occurs : Event.attempt a∈events v.mesh:=event ▸ occ
    have inside : PurchaseInventory.slot x < ar.goods :=
      (v.stock_goods P h width a).symm ▸ slot
    have cap:=(native.1 a occurs) (⟨PurchaseInventory.slot x,inside⟩:Fin ar.goods)
    have span:=v.attempt_room P h width a
    change ar.output+3*ar.goods≤(A).base v.mesh (.attempt a)+(A).stride at span
    have whole:=(A).within v.mesh (.attempt a) occurs
    change RouteSettlement.actual (ProtocolRAMDateSpillRank.attemptBank h N k ar) before (PurchaseInventory.slot x)≤_
    rw [ProtocolRAMDateSpillRank.attempt_read _ _ _ scalar,low _ (by omega)]
    have equal : ar.output+2*ar.goods+PurchaseInventory.slot x=ar.output+ar.goods+ar.goods+PurchaseInventory.slot x:=by omega
    rw [equal,checkout_eq]
    exact cap.trans (Nat.mul_le_mul_right _ (le_max_left ..))
  | feed b=>
    have occurs : Event.feed b∈events v.mesh:=event ▸ occ
    let lay:=feeds b
    let l : Fin (FeedLayout.lanes N k):=⟨PurchaseInventory.lane x,PurchaseInventory.lane_lt x⟩
    have member : lay.column l∈lay.columns:=
      List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩
    have cap:=native.2 b occurs (lay.column l) member (PurchaseInventory.record x)
    have span:=v.feed_room P h width
    have whole:=(A).within v.mesh (.feed b) occurs
    have norm : (lay.column l).overflow+(PurchaseInventory.record x).val=
        (A).base v.mesh (.feed b)+cells+PurchaseInventory.slot x:=by
      change (A).base v.mesh (.feed b)+cells+PurchaseInventory.lane x*2^h+(PurchaseInventory.record x).val=_
      simp [PurchaseInventory.slot,Nat.add_assoc]
    change RouteSettlement.actual (ProtocolRAMDateSpillRank.feedBank lay) before (PurchaseInventory.slot x)≤_
    rw [ProtocolRAMDateSpillRank.feed_read _ _ _ scalar]
    change (before ((lay.column l).overflow+(PurchaseInventory.record x).val)).val≤_
    rw [low _ (by omega),checkout_eq]
    exact cap.trans (Nat.mul_le_mul_right _ (le_max_right ..))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
