import OAI.Hierarchy.TaggedWideNumberedDate
import OAI.Hierarchy.TaggedWireWideFeedOperator
import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProtocolRAMDateSpillSparseShape

namespace OAI
/-! # Original pre- and post-feed sheets split into retained and released wire widths. -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
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

local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
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
local notation "last" => (events v.mesh).length

local notation "pair" => pairKeys (Columns h D) k
open private reportCost reportDates reportEntries reportSites from
  OAI.Hierarchy.TaggedWideNumberedDate

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : reportCost v h width size π raw v.maxBits)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
variable {dates : reportDates v h width size π raw v.maxBits} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
local notation "issues" => reportEntries v h width size π raw bits dates

local notation "who" => reportSites v h width size π raw bits dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

local notation "cardFit" => v.wide_dated_bought_rows h width
local notation "names" => timeRows v.sampler π v.depth days (P).catalogue order cardFit pair
local notation "emb" => DatedRows.embed v.sampler π v.depth days (P).catalogue order cardFit
local notation "catalog" => (P).catalogue.ordinal v.sampler π v.depth days order cardFit
local notation "whereAt" => HistoryRoles.sorted v.sampler π v.depth days
local notation "V" => v.wideDatedValue h width bits mid chk issues

open private feedPresentationRoom from OAI.Hierarchy.TaggedWireWideFeedOperator

include horizon age budget small cost

private theorem spillNumberedAt
    (height : v.wideDatedLedgerHeight ≤ h)
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun a=>(pair a).val))
    (t : ℕ) (bound : t ≤ last) :
    installedWidths (whereAt ∘ names) (V t ∘ emb ∘ names)=
        v.wireAt h width bits π t (StockBound.state C mid t) := by
  let enough:=(v.wide_funded_extent h width bits).trans horizon
  let live:=(v.wide_funded_stock_at_size h width v.radius π raw bits size horizon age budget small).mounted_all
  have addr:=(v.wide_stock_sizes h width ((le_max_right ..).trans age) budget small).words.addresses
  have room:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  have paid:=Classical.choose_spec (Filter.eventually_atTop.1 v.wide_wire_paid) h
    ((le_max_left _ _).trans ((le_max_right _ _).trans height)) width small budget size enough π seed bits
  have ends:=Classical.choose_spec (Filter.eventually_atTop.1 v.wire_paid_ends) h
    ((le_max_right _ _).trans ((le_max_right _ _).trans height)) width small budget size enough π seed bits
  have ledger:=v.dated_wire_of_run h width bits π mid live addr room (small.trans_lt (v.date_prefix_fit h))
    dates (mount).ordinary (mount).centers ord ci original archive receipt paid.1 ends
  exact (v.wide_numbered_date h width size π raw bits horizon age budget small cost (dates := dates) (pos := pos) receipt funded t).trans
      (ledger t bound).symm

/-- At an actual feed, the two chronological public sheets share the retained
width. Their respective low sectors are the released goods and their real paid
core routes. The release amounts are read from the original numbered RAM bank. -/
theorem wide_spill_feed_measured
    (height : v.wideDatedLedgerHeight≤h) (feedHeight : v.feedOperatorHeight≤h)
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun a=>(pair a).val))
    (first : ℕ) (j : Fin last) (b : Boundary) (atFeed : (events v.mesh).get j=.feed b)
    (image : Memory w) (scalar : PurchaseInventory.footprint h N k≤2^w)
    (low : ∀a<(A).endAddress v.mesh,image a=chk a) :
    let page₁:=v.wideSpillPage h width bits first j.val
    let spill:=fun i : Goods h v.W k=>RouteSettlement.actual page₁.overflow image (PurchaseInventory.slot i)
    let entry:=StockBound.state C mid j.val
    let out:=StockBound.state C mid (j.val+1)
    let newMount:=(P).catalogue.coreMount π place order out
    let stockHeight:=(feedPresentationRoom v feedHeight).1
    let dimension:=(feedPresentationRoom v feedHeight).2
    let auth:=v.wide_paid_feed_stock h width size ((v.wide_funded_extent h width bits).trans horizon) v.radius π seed stockHeight budget small dimension
    let cut : Slot C mid (.feed b) ((events v.mesh).take j.val) ((events v.mesh).drop (j.val+1)) entry:=
      (congrArg (fun evt => Slot C mid evt ((events v.mesh).take j.val) ((events v.mesh).drop (j.val+1)) entry) atFeed).mp
        (ordinal_slot C mid j auth.nativeStock.mounted_all)
    let transfer:=v.dated_feed_transfer P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) (sinkBank start cnt r rows) mid auth b cut
    let carry:=FeedTransfer.passWidth newMount (v.wirePaidAt h width bits j.val entry)
      (v.feedPassive (z:=h) width b) (fun a=>supply-v.wireUsedAt h width j.val entry a)
    let goods:=commodityGraph π place
    let rest:=carry+goods.chordWidths transfer.held+goods.chordWidths transfer.kept
    spill=transfer.spill ∧
    installedWidths (whereAt ∘ names) (V j.val ∘ emb ∘ names)=
        rest+(commodityGraph π place).chordWidths spill ∧
    installedWidths (whereAt ∘ names) (V (j.val+1) ∘ emb ∘ names)=
        rest+(mount).actual.chordWidths (routeLoad (mount).ordinary spill) := by
  intro page₁ spill entry out newMount stockHeight dimension auth cut transfer carry goods rest
  let enough:=(v.wide_funded_extent h width bits).trans horizon
  have numbered (t : ℕ) (bound : t≤last) :
      installedWidths (whereAt ∘ names) (V t ∘ emb ∘ names)=
        v.wireAt h width bits π t (StockBound.state C mid t):=
    v.spillNumberedAt h width size π raw horizon age budget small cost (dates := dates) (pos := pos)
      height receipt funded t bound
  have date : (events v.mesh)[j.val]'j.isLt = .feed b := atFeed
  let presents := v.wire_feed_presents h width size enough π seed feedHeight budget small bits j b date
  have oldEq : FeedTransfer.input (π:=π) («place»:=place) carry transfer=v.wireAt h width bits π j.val entry:=presents.choose
  have newEq : FeedTransfer.output newMount carry transfer=v.wireAt h width bits π (j.val+1) out:=presents.choose_spec.choose
  let layout:=FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit b
  have fromTape : spill=transfer.spill:=by
    funext i
    have seen:=v.wire_feed_quantities h width size enough v.radius π seed stockHeight budget small dimension
      j.val j.isLt b date cut i
    have saved : transfer.spill i=(chk (layout.overflow+PurchaseInventory.slot i)).val:=seen.2.2
    rw [saved]
    change RouteSettlement.actual page₁.overflow image (PurchaseInventory.slot i)=_
    dsimp only [page₁]
    rw [v.wide_spill_overflow h width bits first j,atFeed]
    change RouteSettlement.actual (ProtocolRAMDateSpillRank.amountBank h N k layout.overflow) _ _=_
    rw [ProtocolRAMDateSpillRank.amountBank_read _ _ _ scalar]
    have valid:=PurchaseInventory.slot_lt i
    have roomy:=v.feed_room P h width
    have occurs : Event.feed b ∈ events v.mesh := (congrArg (fun event => event ∈ events v.mesh) atFeed).mp ((events v.mesh).get_mem j)
    have within:=(A).within v.mesh (.feed b) occurs
    have offset : layout.overflow=(A).base v.mesh (.feed b)+PurchaseInventory.footprint h N k:=rfl
    have below : layout.overflow + PurchaseInventory.slot i < (A).endAddress v.mesh := calc
      _ < layout.overflow + PurchaseInventory.footprint h N k := Nat.add_lt_add_left valid _
      _ = (A).base v.mesh (.feed b) + 2*PurchaseInventory.footprint h N k := by
        rw [offset, Nat.add_assoc, two_mul]
      _ ≤ _ := (Nat.add_le_add_left roomy _).trans within
    exact congrArg (fun word : Word w => word.val) (low _ below)
  have balance : (fun i=>transfer.old i+transfer.active i)=
      fun i=>transfer.held i+transfer.kept i+transfer.spill i := funext transfer.balanced
  refine ⟨fromTape,?_,?_⟩
  · rw [numbered _ j.isLt.le,←oldEq,fromTape]
    change carry+goods.chordWidths transfer.old+goods.chordWidths transfer.active=
      carry+goods.chordWidths transfer.held+goods.chordWidths transfer.kept+goods.chordWidths transfer.spill
    rw [add_assoc,←chordWidths_add,balance]
    simp only [chordWidths_add,add_assoc]
  · rw [numbered _ j.isLt,←newEq,fromTape]
    change rest+newMount.actual.chordWidths (routeLoad newMount.ordinary transfer.spill)=_
    rw [DatedSpillOffsets.spill_across_mounts v.sampler π (P).catalogue order chk out transfer.spill]

theorem wide_spill_feed_shapes_at
    (height : v.wideDatedLedgerHeight≤h) (feedHeight : v.feedOperatorHeight≤h)
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun a=>(pair a).val))
    (first : ℕ) (j : Fin last) (b : Boundary) (atFeed : (events v.mesh).get j=.feed b)
    (image : Memory w) (scalar : PurchaseInventory.footprint h N k≤2^w)
    (low : ∀a<(A).endAddress v.mesh,image a=chk a) :
    let page₁:=v.wideSpillPage h width bits first j.val
    let spill:=fun i : Goods h v.W k=>RouteSettlement.actual page₁.overflow image (PurchaseInventory.slot i)
    let entry:=StockBound.state C mid j.val
    let out:=StockBound.state C mid (j.val+1)
    let newMount:=(P).catalogue.coreMount π place order out
    let stockHeight:=(feedPresentationRoom v feedHeight).1
    let dimension:=(feedPresentationRoom v feedHeight).2
    let auth:=v.wide_paid_feed_stock h width size ((v.wide_funded_extent h width bits).trans horizon) v.radius π seed stockHeight budget small dimension
    let cut : Slot C mid (.feed b) ((events v.mesh).take j.val) ((events v.mesh).drop (j.val+1)) entry:=
      (congrArg (fun evt => Slot C mid evt ((events v.mesh).take j.val) ((events v.mesh).drop (j.val+1)) entry) atFeed).mp
        (ordinal_slot C mid j auth.nativeStock.mounted_all)
    let transfer:=v.dated_feed_transfer P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) (sinkBank start cnt r rows) mid auth b cut
    let carry:=FeedTransfer.passWidth newMount (v.wirePaidAt h width bits j.val entry)
      (v.feedPassive (z:=h) width b) (fun a=>supply-v.wireUsedAt h width j.val entry a)
    let goods:=commodityGraph π place
    let rest:=carry+goods.chordWidths transfer.held+goods.chordWidths transfer.kept
    installedWidths (whereAt ∘ names) (V j.val ∘ emb ∘ names)=
        rest+(commodityGraph π place).chordWidths spill ∧
    installedWidths (whereAt ∘ names) (V (j.val+1) ∘ emb ∘ names)=
        rest+(mount).actual.chordWidths (routeLoad (mount).ordinary spill) := by
  exact (v.wide_spill_feed_measured h width size π raw horizon age budget small cost (dates := dates) (pos := pos)
    height feedHeight receipt funded first j b atFeed image scalar low).2

theorem wide_spill_feed_shapes
    (height : v.wideDatedLedgerHeight≤h) (feedHeight : v.feedOperatorHeight≤h)
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun a=>(pair a).val))
    (first : ℕ) (j : Fin last) (b : Boundary) (atFeed : (events v.mesh).get j=.feed b)
    (image : Memory w) (scalar : PurchaseInventory.footprint h N k≤2^w)
    (low : ∀a<(A).endAddress v.mesh,image a=chk a) :
    let page₁:=v.wideSpillPage h width bits first j.val
    let spill:=fun i : Goods h v.W k=>RouteSettlement.actual page₁.overflow image (PurchaseInventory.slot i)
    ∃rest : Widths (siteLast h D k+1),
      installedWidths (whereAt ∘ names) (V j.val ∘ emb ∘ names)=
        rest+(commodityGraph π place).chordWidths spill ∧
      installedWidths (whereAt ∘ names) (V (j.val+1) ∘ emb ∘ names)=
        rest+(mount).actual.chordWidths (routeLoad (mount).ordinary spill) := by
  exact ⟨_,v.wide_spill_feed_shapes_at h width size π raw horizon age budget small cost (dates := dates) (pos := pos)
    height feedHeight receipt funded first j b atFeed image scalar low⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
