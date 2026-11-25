import OAI.Hierarchy.ProbeFixedWideTerminalStockCap
import OAI.Hierarchy.ProbeFixedWidePaidTotal
import OAI.Hierarchy.ProbeFixedWidePrefixReceipt
import OAI.Hierarchy.ProbeFinalCongestion

namespace OAI
/-! # Native terminal width at every original edge, after all writes -/

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

/-- Every address in the stock bank or the page of paid widths survives both
real route-directory scans, all chronological owner writes, and reserve settlement. -/
theorem committed_prefix {n : ℕ} (site : Fin n→Fin num) (debit : Fin n→ℕ)
    (ss : List PaidWidths.Slice) (x : ℕ) (low : x<2*2^page) :
    let lastPaid:=PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk
    let archive:=result routes (result ((L).scans v.mesh num) lastPaid)
    ReserveUse.output original old supply site debit archive x=lastPaid x := by
  intro lastPaid archive
  let span:=2^page
  change x<2*span at low
  rw [ReserveUse.frame _ _ _ _ _ _ x
    (.inl (by change x<6*span;omega)) (.inl (by change x<7*span;omega))
    (.inl (by change x<8*span;omega))]
  apply Eq.trans (b:=result ((L).scans v.mesh num) lastPaid x)
  · apply result_below
    intro step hs
    simp only [CoreRoute.stages,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl
    · change x<4*span
      omega
    · change x<5*span
      omega
  · apply result_below
    intro step hs
    obtain ⟨ev,_,rfl⟩:=List.mem_map.mp hs
    change x<2*span+position v.mesh ev*stride
    omega

set_option maxHeartbeats 1000000 in
/-- The original paid width in each slot is augmented by exactly the remaining
stock traversals and unused center traversals, counted with multiplicity. -/
theorem wide_terminal_width_invoice {n : ℕ} (site : Fin n→Fin num) (debit : Fin n→ℕ)
    (cj : Columns h D × Fin k→Fin num) (ss : List PaidWidths.Slice)
    (physical : StockBound.Run C (v.stockBanks P h width) mid h N k (v.keepLimit*width))
    (stored : PaidWidths.Mounted (old).width rows (TerminalLayout.source page) ss chk)
    (wordRoom : 28*2^page<2^w)
    (cost : ∀e : Fin rows,PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    let archive:=result routes (result ((L).scans v.mesh num)
      (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let committed:=ReserveUse.output original old supply site debit archive
    let stockLoad:=fun i=>RouteSettlement.actual (old).stock committed (ci i)
    let surplus:=fun j=>RouteSettlement.actual (old).reserved committed (cj j).val-
      RouteSettlement.actual (old).used committed (cj j).val
    ∀ e : Fin rows,
      ((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width=
        PaidWidths.total ss chk e+routeLoad (mountedBoard).ordinary stockLoad e+routeLoad (mountedBoard).centers surplus e ∧
      PaidWidths.total ss chk e≤((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width ∧
      ((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width≤
        PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width := by
  intro archive receipt committed stockLoad surplus e
  let span:=2^page
  have sizeBound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<span:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at sizeBound
  change 28*span<2^w at wordRoom
  have top : (A).endAddress v.mesh<2^w:=by omega
  have stockCap (i : Commodity (Fin (2^h)) N k) : stockLoad i≤v.keepLimit*width := by
    let z:=PurchaseInventory.slot i
    have ok : z<(stock).size := (PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _)
    have small : (stock).base+z<span:=by omega
    have word : z<2^w:=by omega
    have archiveEq:=v.committed_prefix h width size M π raw site debit ss ((stock).base+z) (by omega)
    have paidEq:=PaidWidths.frame (old).width rows (TerminalLayout.source page) ss chk ((stock).base+z)
      (fun t ht=>(stored t ht).1) (by change (stock).base+z<1*span;omega)
    have auth := v.terminal_stock_at_checkout P h width C mid rfl top physical i
    change ((stock).read committed (z:Word w)).val≤_
    change ((stock).read chk (z:Word w)).val≤_ at auth
    simp only [Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt ok] at auth ⊢
    rw [show committed ((stock).base+z)=chk ((stock).base+z) from archiveEq.trans paidEq]
    exact auth
  have reserveCap (j : Columns h D × Fin k) : RouteSettlement.actual (old).reserved committed (cj j).val ≤ supply :=
    (ReserveUse.reported original old supply site debit archive receipt.archive (cj j)
      receipt.usedSize receipt.reserveSize (receipt.funded _) receipt.word).2.le
  have marginal:=(mountedBoard).final_return_bound stockLoad
    (fun j=>RouteSettlement.actual (old).reserved committed (cj j).val)
    (fun j=>RouteSettlement.actual (old).used committed (cj j).val) v.keepLimit (fuel v.mesh) width stockCap reserveCap e
  have stagesFixed : Stages h (2^v.W) = publicStages v.W := fixed_stage_count h v.W
  conv_rhs at marginal => rw [stagesFixed]
  change routeLoad (mountedBoard).ordinary stockLoad e+routeLoad (mountedBoard).centers surplus e≤
    (v.overflowFactor v.keepLimit+fuel v.mesh)*width at marginal
  have within : rows<span := by omega
  have fit : (old).width.base+e.val<2*span := by change 1*span+e.val<2*span;have := e.isLt;omega
  have read:=v.committed_prefix h width size M π raw site debit ss _ fit
  have paid := (congrArg Fin.val read).trans (PaidWidths.read (old).width (TerminalLayout.source page) ss chk e
    (fun t ht=>(stored t ht).1) ((Nat.le_add_right ..).trans_lt (cost e)))
  have bill := (Nat.add_le_add_left marginal (PaidWidths.total ss chk e)).trans_lt (cost e)
  have result:=(sink).terminal_width committed ord ci (fun j=>(cj j).val) e
    (by change rows ≤ span;omega) (by omega) (by change 1*span+rows≤9*span;omega)
    (by change (committed ((old).width.base+e.val)).val+_ < _;rw [paid];exact bill)
  change (committed ((old).width.base+e.val)).val=_ at paid
  change ((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width =
    (committed ((old).width.base+e.val)).val + routeLoad (mountedBoard).ordinary stockLoad e +
      routeLoad (mountedBoard).centers surplus e at result
  rw [paid] at result
  exact ⟨result,by rw [result];omega,by rw [result];omega⟩

/-- The original paid width in each slot is augmented by exactly the remaining
stock traversals and unused center traversals, counted with multiplicity. -/
theorem wide_terminal_width_at {n : ℕ} (site : Fin n→Fin num) (debit : Fin n→ℕ)
    (cj : Columns h D × Fin k→Fin num) (ss : List PaidWidths.Slice)
    (physical : StockBound.Run C (v.stockBanks P h width) mid h N k (v.keepLimit*width))
    (stored : PaidWidths.Mounted (old).width rows (TerminalLayout.source page) ss chk)
    (wordRoom : 28*2^page<2^w)
    (cost : ∀e : Fin rows,PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    let archive:=result routes (result ((L).scans v.mesh num)
      (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let committed:=ReserveUse.output original old supply site debit archive
    let stockLoad:=fun i=>RouteSettlement.actual (old).stock committed (ci i)
    let surplus:=fun j=>RouteSettlement.actual (old).reserved committed (cj j).val-
      RouteSettlement.actual (old).used committed (cj j).val
    ∀ e : Fin rows,
      ((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width=
        PaidWidths.total ss chk e+routeLoad (mountedBoard).ordinary stockLoad e+routeLoad (mountedBoard).centers surplus e ∧
      PaidWidths.total ss chk e≤((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width := by
  intro archive receipt committed stockLoad surplus e
  have sum:=v.wide_terminal_width_invoice h width size M π raw site debit cj ss physical stored wordRoom cost receipt e
  exact ⟨sum.1,sum.2.1⟩

/-- Turn the exact physical width equality into a strict natural-word bound on
the complete bill, including both returns, before any final native cast. -/
theorem native_terminal_width_fit {W r' edgeCount : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edgeCount)} {centers : J→List (Fin edgeCount)}
    (K : Sink r' edgeCount) (m : Memory W) (enum : Fin r'≃RouteOccurrence core centers)
    (i : I→ℕ) (j : J→ℕ) (e : Fin edgeCount) (mass : ℕ)
    (read : (K.terminalRows m enum i j e).width=mass) : mass<2^W := by
  rw [←read]
  exact Fin.isLt _

/-- Convert the last original prefix read of the fixed native reporter into
the inequality on its actual addressable bank, also for rows of width zero. -/
theorem wide_prefix_bank_le_width (compile : Event→List PaidWidths.Slice) (final : Memory w)
    (originalRows : Fin rows→ProtocolRAMEmit.Row)
    (word : rows≤2^w)
    (read : ∀e : Fin rows,
      (final (((v.wideWidthLayout h width ((events v.mesh).flatMap compile)).bank last).base+e.val)).val=
      PaidWidths.total (PrefixWidths.prefixRows (events v.mesh) compile last) chk e)
    (paid : ∀e : Fin rows, PaidWidths.total ((events v.mesh).flatMap compile) chk e≤(originalRows e).width)
    (e : Fin rows) :
    (((v.wideWidthLayout h width ((events v.mesh).flatMap compile)).bank last).read final
      (e.val:Word w)).val≤(originalRows e).width := by
  let l:=v.wideWidthLayout h width ((events v.mesh).flatMap compile)
  have slot : e.val<(l.bank last).size:=e.isLt.trans_le l.covered
  change ((l.bank last).read final (e.val:Word w)).val ≤ (originalRows e).width
  simp only [Bank.read,Fin.val_cast_of_lt (e.isLt.trans_le word),Nat.mod_eq_of_lt slot]
  have full : (final ((l.bank last).base+e.val)).val=
      PaidWidths.total ((events v.mesh).flatMap compile) chk e := by
    simpa only [PrefixWidths.prefixRows,List.take_length] using read e
  exact full.le.trans (paid e)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
