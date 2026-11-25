import OAI.Hierarchy.ProbeFixedWideReportedWidth
import OAI.Hierarchy.ProtocolRAMCataloguePaidSupport

namespace OAI
/-! # Purchased support of the native terminal graph -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
set_option maxRecDepth 8192
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
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => Boot.booted market size (v.wideSignedWords h width stock M π o raw)
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw



local notation "place" => siteNumber h D k
local notation "mountedBoard" => (P).catalogue.coreMount π place (v.wideOrder h width) chk
local notation "ord" => CoreRoute.enum mountedBoard o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i

set_option maxHeartbeats 1000000 in
/-- A physically positive purchased output row must have been activated.
Both terminal route families traverse only original permanent row ordinals. -/
theorem wide_bought_activated {n : ℕ} (site : Fin n→Fin num) (debit : Fin n→ℕ)
    (cj : Columns h D × Fin k→ℕ) (ss : List PaidWidths.Slice)
    (support : ∀ slice∈ss,(P).catalogue.Supported slice chk)
    (installed : ∀ slice∈ss,slice.Fits (old).width rows (TerminalLayout.source page) w)
    (words : 28*2^page<2^w) :
    let archive:=result routes (result ((L).scans v.mesh num)
      (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let committed:=ReserveUse.output original old supply site debit archive
    ∀j : Fin (P).catalogue.boughtRows,
      0<((sink).terminalRows committed ord ci cj ((P).catalogue.boughtIndex j)).width →
      (P).catalogue.bought.flag.eval chk (j.val:Word w)≠0 := by
  intro archive committed j positive off
  let span:=2^page
  let e:=(P).catalogue.boughtIndex j
  have packed : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<span := Nat.lt_log2_self
  unfold TerminalLayout.footprint at packed
  have small : rows<span := by omega
  change 28*span<2^w at words
  have room : 0<2^w:=Nat.two_pow_pos _
  have empty:= (P).catalogue.no_dormant_load ss chk j support off
  have cap : PaidWidths.total ss chk e<2^w := empty.trans_lt room
  have before:=v.committed_prefix h width size M π raw site debit ss ((old).width.base+e.val)
    (by change 1*span+e.val<2*span;have :=e.isLt;omega)
  have widthZero : (committed ((old).width.base+e.val)).val=0 :=
    (congrArg Fin.val before).trans ((PaidWidths.read (old).width (TerminalLayout.source page) ss chk e installed cap).trans empty)
  let hold:=fun i : Commodity (Fin (2^h)) N k =>RouteSettlement.actual (old).stock committed (ci i)
  let excess:=fun u : Columns h D × Fin k =>RouteSettlement.actual (old).reserved committed (cj u)-RouteSettlement.actual (old).used committed (cj u)
  have paths : (mountedBoard).ordinary=fun i=>
      ((commodityWalk (S:=v.sampler) π i).map (order).symm).map (P).catalogue.coreIndex :=
    funext ((P).catalogue.coreMount_ordinary π place order chk)
  have centers : (mountedBoard).centers=fun u=>
      ((catalystWalk (S:=v.sampler) u).map (order).symm).map (P).catalogue.coreIndex :=
    funext ((P).catalogue.coreMount_centers π place order chk)
  have coreZero : routeLoad (mountedBoard).ordinary hold e=0 := by
    rw [paths]
    exact (P).catalogue.core_route_disjoint _ hold j
  have centerZero : routeLoad (mountedBoard).centers excess e=0 := by
    rw [centers]
    exact (P).catalogue.core_route_disjoint _ excess j
  have out:= (sink).terminal_width committed ord ci cj e
    (by change rows ≤ span;omega) (by omega) (by change 1*span+rows≤9*span;omega)
    (by change (committed ((old).width.base+e.val)).val+(routeLoad (mountedBoard).ordinary hold e+
          routeLoad (mountedBoard).centers excess e)<2^w
        simpa only [widthZero,coreZero,centerZero,Nat.add_zero] using room)
  change ((sink).terminalRows committed ord ci cj e).width=
    (committed ((old).width.base+e.val)).val+routeLoad (mountedBoard).ordinary hold e+routeLoad (mountedBoard).centers excess e at out
  rw [widthZero,coreZero,centerZero] at out
  exact (Nat.ne_of_gt positive) out

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
