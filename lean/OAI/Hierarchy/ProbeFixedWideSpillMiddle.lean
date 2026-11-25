import OAI.Hierarchy.ProbeFinalCongestion
import OAI.Hierarchy.ProbeFixedWideDatedCost
import OAI.Hierarchy.TaggedWideDatedSpillMiddle
import OAI.Hierarchy.ProtocolRAMDateSpillLoadRead
import OAI.Hierarchy.ProbeFixedWideSpillCases

namespace OAI
/-! # The preclip amounts at each dated original role -/
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

def wideSpillMiddle (j : ℕ) (region : DateSpill.Page) : Expr :=
  DatedRoleInput.spillMiddle (v.wideRoleInventory h width bits (j+1))
    (v.wideRoleWidth h width bits (j+1)) region.load region.overflow

theorem wide_spill_middle_work_eq (j : ℕ) (region : DateSpill.Page) :
    (v.wideSpillMiddle h width bits j region).work=4*(v.wideRoleWidth h width bits (j+1)).work+58 := by
  unfold wideSpillMiddle
  rw [DatedRoleInput.spillMiddle_work]
  change 2*7+4*_+3*7+23=_
  omega

theorem wide_spill_middle_work (j : ℕ) (region : DateSpill.Page) :
    (v.wideSpillMiddle h width bits j region).work≤4*v.wideRoleWorkBound+58 := by
  rw [v.wide_spill_middle_work_eq]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 ((v.wide_role_work_at h width bits).2 (j+1))) _

theorem wide_spill_middle_fits (j : ℕ) (date : j<last) (region : DateSpill.Page) (dest : ℕ)
    (prefixRoom : (lr).scratch≤dest) (word : dest<2^w) (rank : region.offsetsStart≤dest)
    (wasted : region.overflow.base+region.overflow.size≤dest) :
    (v.wideSpillMiddle h width bits j region).Fits w dest := by
  have terms:=v.wide_role_fits h width bits (j+1) date dest prefixRoom word
  have mk (b : Bank) (bound : b.base+b.size≤dest) : b.Fits w dest :=
    ⟨Nat.two_pow_pos _,by omega,bound⟩
  exact DatedRoleInput.spillMiddle_fits _ _ _ _ terms.1.1 terms.1.2.2.1 terms.2
    (mk _ (region.load_end.trans rank)) (mk _ wasted)

/-- For all admissible widths one public date height bound suffices for the
additional commodity amount read from the native overflow column. -/
def wideSpillAmountHeight := 2*v.keepLimit+1+max v.menu.maximum (v.keepLimit+1)

theorem wide_spill_mul_room (factor : ℕ) (large : factor≤h) (small : width≤2^h) : factor*width<2^w := by
  have cap:=large.trans_lt (Nat.lt_two_pow_self (n:=h))
  have expo : h+h≤w:=by unfold Native.wordBits ProbeStage.roomBits;omega
  calc
    _≤factor*2^h:=Nat.mul_le_mul_left _ small
    _ <2^h*2^h:=Nat.mul_lt_mul_of_pos_right cap (Nat.two_pow_pos _)
    _=2^(h+h):=(pow_add ..).symm
    _≤2^w:=Nat.pow_le_pow_right (by decide) expo

theorem wide_spill_add_room (large : v.wideSpillAmountHeight≤h) (small : width≤2^h) :
    (2*v.keepLimit+1)*width+max v.menu.maximum (v.keepLimit+1)*width<2^w := by
  rw [←Nat.add_mul]
  exact v.wide_spill_mul_room h width _ large small

theorem wide_spill_held_bound (initial : Memory w) (j : ℕ) (hj : j≤last)
    (bounded : StockBound.Run C (v.stockBanks P h width) initial h N k (v.keepLimit*width))
    (i : Goods h v.W k) :
    DatedRoleInput.currentFlow v P h width r old source table target owners j initial i≤(2*v.keepLimit+1)*width :=
  commodity_held_cap v.mesh width v.keepLimit _ _ _ _ i _
    (v.prefix_active_bound P h width r old source table target owners initial j hj bounded i)
    (v.prefix_stash_bound P h width r old source table target owners initial j hj bounded i)

set_option maxRecDepth 8192

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "mount" => (P).catalogue.coreMount π (siteNumber h D k) order chk
local notation "value" => v.wideDatedValue h width bits mid chk

theorem wide_spill_route_bound (region : DateSpill.Page) (m : Memory w)
    (limit : ∀x : Goods h v.W k,RouteSettlement.actual region.overflow m (PurchaseInventory.slot x)≤
      max v.menu.maximum (v.keepLimit+1)*width)
    (e : Fin rows) :
    routeLoad (mount).ordinary (fun x=>RouteSettlement.actual region.overflow m (PurchaseInventory.slot x)) e≤
      v.overflowFactor (max v.menu.maximum (v.keepLimit+1))*width := by
  let cap:=max v.menu.maximum (v.keepLimit+1)
  have all:=(mount).final_return_bound (fun x=>RouteSettlement.actual region.overflow m (PurchaseInventory.slot x))
    (fun _=>0) (fun _=>0) cap 0 width limit (fun _=>Nat.zero_le _) e
  have bound:=Nat.le_trans (Nat.le_add_right ..) all
  simpa only [Stages,fixed_stage_count,Nat.add_zero,overflowFactor] using bound

theorem wide_spill_route_room (region : DateSpill.Page) (m : Memory w)
    (limit : ∀x : Goods h v.W k,RouteSettlement.actual region.overflow m (PurchaseInventory.slot x)≤
      max v.menu.maximum (v.keepLimit+1)*width)
    (large : v.overflowFactor (max v.menu.maximum (v.keepLimit+1))≤h) (small : width≤2^h) (e : Fin rows) :
    routeLoad (mount).ordinary (fun x=>RouteSettlement.actual region.overflow m (PurchaseInventory.slot x)) e<2^w :=
  (v.wide_spill_route_bound h width bits size M π raw region m limit e).trans_lt
    (v.wide_spill_mul_room h width _ large small)

/-- The compiled paid subtraction reads every visit to its wire from the
actual rank-counter output, including repeated visits by the same commodity. -/
theorem wide_spill_middle_read (j : ℕ) (date : j<last) (region : DateSpill.Page) (before final : Memory w)
    (issues : Attempt→CatalystArchive.Entry num width)
    (pages : v.WideDatedPages h width bits mid chk final issues) (active : v.WideHistorySupport h width chk bits)
    (stockRun : StockBound.Run C (v.stockBanks P h width) mid h N k (v.keepLimit*width))
    (sameEdges : region.edges=rows) (sameCore : region.core=ProtocolRAMDateSpillRank.coreCount o)
    (rank : ProtocolRAMDateSpillRank.RankRead mount o region.rankStart region.overflow before final)
    (low : region.overflow.base+region.overflow.size≤region.rankStart)
    (priceRoom : ∀e,routeLoad (mount).ordinary
      (fun x=>RouteSettlement.actual region.overflow before (PurchaseInventory.slot x)) e<2^w)
    (limit : ∀x : Goods h v.W k,RouteSettlement.actual region.overflow before (PurchaseInventory.slot x)≤
      max v.menu.maximum (v.keepLimit+1)*width)
    (age : v.wideSpillAmountHeight≤h) (small : width≤2^h) (i : Fin K) :
    ((v.wideSpillMiddle h width bits j region).eval final (i.val:Word w)).val=
      FeedTransfer.middleAmounts mount (value issues (j+1))
        (fun x=>RouteSettlement.actual region.overflow before (PurchaseInventory.slot x)) (SettledMatrix.Layout.numbered i) := by
  have key:=DatedRoleInput.decoded base final ((lw).bank (j+1)) ((lw).bank (j+1))
    (PrefixReserve.banks lr old (j+1)).reserved (PrefixReserve.banks lr old (j+1)).used pages.metadata pages.physical i
  have word : rows≤2^w:=by
    have card:=v.wide_old_rows h width
    have cap:=pages.physical
    omega
  have count:=ProtocolRAMDateSpillRank.read_load mount o region before final sameEdges sameCore rank word priceRoom
  have spill (x : Goods h v.W k) : (region.overflow.read final ((PurchaseInventory.slot x):Word w)).val=
      RouteSettlement.actual region.overflow before (PurchaseInventory.slot x):=by
    apply congrArg Fin.val
    unfold Bank.read
    apply rank.frame
    exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos region.overflow.bits)) _).trans_le low
  have enough:=v.wide_spill_add_room h width age small
  have wide : 2<2^w:=by
    apply lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) ?_)
    unfold Native.wordBits
    omega
  apply DatedRoleInput.spillMiddle_read _ _ _ _ final i _ _ _ wide key
    (v.wide_role_width_at h width bits mid chk final issues pages active (j+1) date i) count spill
  intro x
  exact (Nat.add_le_add (v.wide_spill_held_bound h width mid (j+1) date stockRun x) (limit x)).trans_lt enough

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
