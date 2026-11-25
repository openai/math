import OAI.Hierarchy.ProbeFixedWideSpillChartSectors
import OAI.Hierarchy.TaggedWireWideGoodsChange
import OAI.Hierarchy.ProbeFixedWideSpillMiddleBounds

namespace OAI
/-! # An earlier-live spill occupies its original full goods seat at both kinds of date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU StripDirectory
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "boards₀" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards₀ v.mesh (P).catalogue (P).routes F A)
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
local notation "L" => ownerLedger boards₀ v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts boards₀ v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F boards₀ v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "headerWidth" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups headerWidth R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups headerWidth R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups headerWidth

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight≤h)
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
    (A₀ : WideFundedTurnAlignment v h width size M π raw v.maxBits issues who cj marks)

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

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "target" => v.wideCorrectedWidths h width size M π raw bits issues first input
local notation "region" => v.wideSpillPage h width bits first
open DatedSpillOffsets
local notation "degs" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "Gds" => Goods h v.W k
local notation "Cts" => Catalysts h v.W k
local notation "Cat" => Catalogue v.sampler π v.depth marks
local notation "clip" => fun j : Fin last=>fun x : Gds=>
  RouteSettlement.actual (region j.val).overflow (input j) (PurchaseInventory.slot x)
local notation "orig" => fun j : Fin (last+1)=>(value j.val ∘ embedded ∘ names)
local notation "post" => fun j : Fin last=>orig j.succ
local notation "pre" => fun j : Fin last=>
  if (correct).attempt j then target 0 j.succ ∘ embedded ∘ names else orig j.castSucc
local notation "sparseBefore" => fun j : Fin last=>((Sum.elim (fun _:Cat=>0) (Sum.elim (clip j) (fun _:Cts=>0))) ∘ names)
local notation "sparseAfter" => fun j : Fin last=>
  ((Sum.elim (fun e:Cat=>routeLoad (mount).ordinary (clip j) (ordinal e)) (fun _:Gds⊕Cts=>0)) ∘ names)
local notation "ids" => fun i=>(sparse (names i)).val
local notation "cert" => SectorRead v.sampler π v.depth marks unique (P).catalogue order bsize axis oldRows

/-- On a feed the original pre-date stock includes the goods about to be
spilled. The earlier deposit can be final-width zero. -/
theorem wide_spill_chart_goods_live (j : Fin last) (i : Gds)
    (extent : (A).endAddress v.mesh≤ size) (height : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (scalar : PurchaseInventory.footprint h N k≤2^w) (low : ∀a<(A).endAddress v.mesh,input j a=chk a)
    (live : 0<clip j i) :
    0<pre j ((names).symm (.inr (.inl i))) := by
  let vtx:=(names).symm (.inr (.inl i))
  have identifies : embedded (names vtx)=.inr (.inl i):=by
    change embedded (names ((names).symm _))=_
    rw [Equiv.apply_symm_apply]
    rfl
  cases atEvent:(events v.mesh).get j with
  | attempt a=>
    have yes : (correct).attempt j=true:=by change (match (events v.mesh).get j with | .attempt _=>true | .feed _=>false)=_;rw [atEvent]
    simp only [ite_eq_left yes,wideCorrectedWidths,Fin.cases_succ,Function.comp_apply]
    change 0<FeedTransfer.middleAmounts mount (value (j.val+1)) (clip j) (embedded (names vtx))
    rw [identifies]
    change 0<_+clip j i
    omega
  | feed b=>
    have no : (correct).attempt j=false:=by change (match (events v.mesh).get j with | .attempt _=>true | .feed _=>false)=_;rw [atEvent]
    have notYes : ¬(correct).attempt j=true:=by rw [no];decide
    simp only [ite_eq_right notYes,Function.comp_apply]
    change 0<value j.val (embedded (names vtx))
    rw [identifies]
    have run:=v.wide_paid_feed_stock h width size extent M π seed height budget small dimension
    let entry:=StockBound.state C mid j.val
    have date : (events v.mesh)[j.val]=.feed b:=atEvent
    have cut : Slot C mid (.feed b) ((events v.mesh).take j.val) ((events v.mesh).drop (j.val+1)) entry:=by
      exact (congrArg (fun evt => Calendar.Slot C mid evt ((events v.mesh).take j.val)
        ((events v.mesh).drop (j.val+1)) entry) date).mp
        (ordinal_slot C mid j run.nativeStock.mounted_all)
    let transfer:=v.dated_feed_transfer P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
      (TerminalLayout.destination page) (sinkBank start cnt r rows) mid run b cut
    let layout:=FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit b
    have receipt:=v.wire_feed_quantities h width size extent M π seed height budget small dimension j.val j.isLt b date cut i
    have boughtFlow : v.wireGoodsAt h width j.val entry i=v.feedPassive («z»:=h) width b i+transfer.old i+transfer.active i:=receipt.1
    have remembered : transfer.spill i=(chk (layout.overflow+PurchaseInventory.slot i)).val:=receipt.2.2
    have spillEq : clip j i=transfer.spill i:=by
      rw [remembered]
      change RouteSettlement.actual (region j.val).overflow (input j) (PurchaseInventory.slot i)=_
      rw [v.wide_spill_overflow h width bits first j,atEvent]
      change RouteSettlement.actual (ProtocolRAMDateSpillRank.amountBank h N k layout.overflow) _ _=_
      rw [ProtocolRAMDateSpillRank.amountBank_read _ _ _ scalar]
      have slot:=PurchaseInventory.slot_lt i
      have room:=v.feed_room P h width
      have occurs : Event.feed b∈events v.mesh:=atEvent ▸ (events v.mesh).get_mem j
      have before:=(A).within v.mesh (.feed b) occurs
      have addr : layout.overflow=(A).base v.mesh (.feed b)+PurchaseInventory.footprint h N k:=rfl
      exact congrArg Fin.val (low _ (by rw [addr]; omega))
    have positive : 0<transfer.spill i:=spillEq ▸ live
    have status:=transfer.balanced i
    have mag : 0<v.wireGoodsAt h width j.val entry i:=by omega
    exact (congrArg (fun amount : ℕ => 0 < amount) (v.wire_goods_run h width j.val mid i)).mp mag

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
