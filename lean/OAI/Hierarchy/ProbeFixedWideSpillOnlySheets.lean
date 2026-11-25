import OAI.Hierarchy.ProbeFixedWideSpillEvent
import OAI.Hierarchy.ProbeFixedWideSpillOnly
import OAI.Hierarchy.TaggedWireDatedLedger
import OAI.Hierarchy.ProbeFixedWideDatedSheetReads
import OAI.Hierarchy.ProbeFixedWideSpillMiddleSheets

namespace OAI
/-! # Physical endpoint and amount sheets for the intermediate dated capped pass -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
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


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (card : recordCount v.mesh issues = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k))
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R»:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "z" => shape
local notation "ports" => livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "value" => v.wideDatedValue h width bits mid chk issues
local notation "tb" => v.wideTerminalBoard h width bits 0

local notation "bsize" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π v.depth marks (P).catalogue order bsize axis
local notation "ordinal" => (P).catalogue.ordinal v.sampler π v.depth marks order bsize
local notation "embedded" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order bsize
local notation "sparse" => sparseKey v.sampler π v.depth marks (P).catalogue order bsize
  (PurchaseInventory.slotEquiv h N k) axis
local notation "partialRow" => DatedRows.lookup v.sampler π v.depth marks (P).catalogue order bsize names
local notation "direction" => DatedRows.inputSide v.sampler π v.depth marks names
local notation "siteCount" => siteLast h D k+1

include horizon age budget small operandAge card A₀
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
theorem wide_spill_only_sheet_reads (m rankedInput : Memory w) (basePage : ℕ) (j : Fin last)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    (input : ∀x<(A).endAddress v.mesh,rankedInput x=chk x)
    (rank : let region:=v.wideSpillPage h width bits basePage j.val
      ProtocolRAMDateSpillRank.RankRead mount o region.rankStart region.overflow rankedInput m)
    (heap : (v.wideReserveLayout h width ss).scratch≤basePage)
    (side : Bool)
    (paidAge : v.wideSpillPaidHeight≤h)
    (ell unitCost rom : ℕ)
    (strides : ∀x : Fin siteCount,((v.wideDated h width ell unitCost).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w)) :
    let region:=v.wideSpillPage h width bits basePage j.val
    let spill:=fun x : Goods h v.W k=>RouteSettlement.actual region.overflow rankedInput (PurchaseInventory.slot x)
    let target : Old h v.W k rows→ℕ:=Sum.elim (fun e=>if side then routeLoad (mount).ordinary spill e else 0)
      (Sum.elim (fun x=>if side then 0 else spill x) (fun _=>0))
    DatedRoleSheets.Reads oldRows ((z).chart hi) ((tb).before) ((v.wideDated h width ell unitCost).siteStride rom)
      (WideCPU.spillOnly (v.wideRoleInventory h width bits (j.val+1)) region side) (v.wideRoleID h width bits) v.sampler π v.depth marks unique names m
      (target ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) partialRow direction := by
  intro region spill target
  have extent:=(v.wide_funded_extent h width bits).trans horizon
  obtain ⟨⟨amount,loads⟩,⟨supportAge,overflowAge⟩⟩ :=
    (show (v.wideSpillAmountHeight≤h ∧ v.overflowFactor (max v.menu.maximum (v.keepLimit+1))≤h) ∧
      v.wideDatedSupportHeight≤h ∧ v.wideSpillOverflowHeight≤h by simpa only [wideSpillSheetHeight,max_le_iff] using large)
  have cap:=pages.physical
  have labels:=v.wide_old_rows h width
  have cells : PurchaseInventory.footprint h N k≤2^w:=by omega
  have limit:=v.wide_spill_overflow_bound h width bits size M π raw basePage j rankedInput overflowAge extent
    floor small budget cells rad accepted input
  have priceRoom:=v.wide_spill_route_room h width bits size M π raw region rankedInput limit loads small
  have observed:=v.wide_spill_only_read h width bits size M π raw j.val region rankedInput m issues pages
    rfl rfl rank (v.wide_spill_page_below h width bits basePage j
      (Nat.le_of_succ_le ((v.wide_prefix_low_heap h width bits).trans heap))) priceRoom side
  have invoice (e : Fin rows) : routeLoad (mount).ordinary spill e ≤
      PaidWidths.total (v.wideEventSlices h width bits ((events v.mesh).get j)) chk e := by
    subst M
    exact v.wide_spill_event_le h width bits size π raw basePage j rankedInput paidAge extent small budget input e
  have counted (e : Fin rows) : target (.inl e)≤counts e := by
    cases side with
    | false => exact Nat.zero_le _
    | true =>
      apply (invoice e).trans
      apply le_trans _ (v.wide_dated_paid_le h width size M π raw bits horizon age budget small issues who cj
        baseline cost (j.val+1) e)
      change _≤v.wirePaidAt h width bits (j.val+1) chk e
      rw [v.wire_paid_next h width bits j chk e]
      exact Nat.le_add_left ..
  exact v.wide_sheet_reads_of_counts h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ m pages keep highFit (WideCPU.spillOnly (v.wideRoleInventory h width bits (j.val+1)) region side) target observed counted ell unitCost rom strides

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
omit operandAge A₀ card in
/-- Every earlier spill traversal is funded in the literal terminal paid-edge report. -/
theorem wide_spill_turn_invoice (basePage : ℕ) (j : Fin last) (rankedInput : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (input : ∀x,x<(A).endAddress v.mesh→ rankedInput x=chk x) (e : Fin rows) :
    let region:=v.wideSpillPage h width bits basePage j.val
    routeLoad (mount).ordinary (fun good=>RouteSettlement.actual region.overflow rankedInput (PurchaseInventory.slot good)) e≤counts e := by
  intro region
  have billed : routeLoad (mount).ordinary (fun good=>RouteSettlement.actual region.overflow rankedInput (PurchaseInventory.slot good)) e≤
      PaidWidths.total (v.wideEventSlices h width bits ((events v.mesh).get j)) chk e := by
    subst M
    exact v.wide_spill_event_le h width bits size π raw basePage j rankedInput paidAge
      ((v.wide_funded_extent h width bits).trans horizon) small budget input e
  apply billed.trans
  apply le_trans _ (v.wide_dated_paid_le h width size M π raw bits horizon age budget small issues who cj baseline cost (j.val+1) e)
  change _≤v.wirePaidAt h width bits (j.val+1) chk e
  rw [v.wire_paid_next h width bits j chk e]
  exact Nat.le_add_left ..

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
