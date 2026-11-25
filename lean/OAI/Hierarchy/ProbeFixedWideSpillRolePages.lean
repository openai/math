import OAI.Hierarchy.ProbeFixedWideSpillOnlySheets
import OAI.Hierarchy.ProbeFixedWideSpillRoleFits
import OAI.Hierarchy.TaggedWideOriginalRoleFacts
import OAI.Hierarchy.ProbeFixedWideSpillRankRun

namespace OAI
/-! # The three actual date-indexed row families consumed by capped and feed turns -/
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

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
variable (first : ℕ) (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "region" => v.wideSpillPage h width bits first
local notation "clip" => fun j : Fin last=>fun x : Goods h v.W k=>
  RouteSettlement.actual (region j.val).overflow (input j) (PurchaseInventory.slot x)

/-- Width before a commodity cap, or the amounts of just the incoming
goods/outgoing core roles used by the real spill comparator. -/
def wideCorrectedWidths (f : Fin 3) : Fin (last+1)→Old h v.W k rows→ℕ :=
  Fin.cases (fun _=>0) fun j=>
    if f=0 then FeedTransfer.middleAmounts mount (value (j.val+1)) (clip j)
    else Sum.elim (fun e=>if f=2 then routeLoad (mount).ordinary (clip j) e else 0)
      (Sum.elim (fun x=>if f=2 then 0 else clip j x) (fun _=>0))

local notation "quant" => v.wideCorrectedWidths h width size M π raw bits issues first input
include horizon age budget small operandAge card A₀
theorem wide_spill_role_observed (m : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    (mounted : ∀j,∀x<(A).endAddress v.mesh,input j x=chk x)
    (rank : ∀j : Fin last,ProtocolRAMDateSpillRank.RankRead mount o (region j.val).rankStart
      (region j.val).overflow (input j) m)
    (heap : (v.wideReserveLayout h width ss).scratch≤first)
    (paidAge : v.wideSpillPaidHeight≤h) (ell unitCost rom : ℕ)
    (strides : ∀x : Fin siteCount,((v.wideDated h width ell unitCost).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w))
    (f : Fin 3) (t : Fin (last+1)) :
    let layout:=v.wideSpillDates h width ell unitCost bits first
    DatedRoleSheets.Reads oldRows ((z).chart hi) ((tb).before) ((v.wideDated h width ell unitCost).siteStride rom)
      ((layout.roles f).amount t) (v.wideRoleID h width bits) v.sampler π v.depth marks unique names m
      (quant f t ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) partialRow direction := by
  intro layout
  induction t using Fin.cases with
  | zero=>
    apply v.wide_sheet_reads_of_counts h width size M π raw bits horizon age budget small operandAge issues card who cj
      marks unique A₀ m pages keep highFit (.lit 0) (fun _=>0) _ _ ell unitCost rom strides
    · intro i; simp [Expr.eval]
    · exact fun _=>Nat.zero_le _
  | succ j=>
    by_cases middle : f=0
    · subst f
      simpa only [layout,WideCPU.SpillDates.roles,wideCorrectedWidths,Fin.cases_succ,ite_true,
        wideSpillDates] using v.wide_spill_middle_sheet_reads h width size M π raw bits horizon age budget small
          operandAge issues card who cj marks unique A₀ m (input j) first j pages baseline keep cost highFit large rad
          floor accepted (mounted j) (rank j) heap ell unitCost rom strides
    · have side:=v.wide_spill_only_sheet_reads h width size M π raw bits horizon age budget small operandAge issues
        card who cj marks unique A₀ m (input j) first j pages baseline keep cost highFit large rad floor accepted
        (mounted j) (rank j) heap (decide (f=2)) paidAge ell unitCost rom strides
      by_cases paidSide : f=2 <;>
        simpa [layout,WideCPU.SpillDates.roles,wideCorrectedWidths,wideSpillDates,middle,paidSide] using side

theorem wide_spill_role_issued (m : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    (mounted : ∀j,∀x<(A).endAddress v.mesh,input j x=chk x)
    (rank : ∀j : Fin last,ProtocolRAMDateSpillRank.RankRead mount o (region j.val).rankStart
      (region j.val).overflow (input j) m)
    (heap : (v.wideReserveLayout h width ss).scratch≤first)
    (paidAge : v.wideSpillPaidHeight≤h) (ell unitCost rom : ℕ)
    (strides : ∀x : Fin siteCount,((v.wideDated h width ell unitCost).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w))
    (funded : v.wideFundedSize h width v.maxBits≤v.wideSpillRankEnd h width bits first)
    (strideFit : rom+ProtocolRAMPurchaseSampler.span siteCount≤v.wideSpillRankEnd h width bits first)
    (ordinary : bits=v.maxBits)
    (room : (v.wideSpillDates h width ell unitCost bits first).endAt (v.wideSpillRankEnd h width bits first)<2^w)
    (f : Fin 3) (t : Fin (last+1)) (field : Fin 3) :
    let layout:=v.wideSpillDates h width ell unitCost bits first
    let basePage:=v.wideSpillRankEnd h width bits first
    let sub:=layout.roles f
    let root:=layout.roleRoot basePage f
    let qty:=(fun j : Fin (last+1)=>quant f j ∘ embedded ∘ names)
    let id:=fun i=>(sparse (names i)).val
    (sub.roleResult rom root v.sampler π v.depth marks unique names qty id rfl t field).Issued basePage m := by
  subst bits
  intro layout basePage sub root qty id now low
  have before : basePage≤root:=Nat.le_add_right ..
  have endAt : sub.rolesEnd root≤layout.endAt basePage:=by
    dsimp only [root,sub,WideCPU.SpillDates.roleRoot,WideCPU.SpillDates.roles,WideCPU.Dated.rolesEnd,
      WideCPU.SpillDates.endAt,WideCPU.Dated.maskStart,WideCPU.Dated.controlStart,WideCPU.endOf]
    have a:=Nat.mul_le_mul_right ((last+1)*(3*layout.original.roleSpan)) (show f.val≤2 by omega)
    change basePage+f.val*((last+1)*(3*layout.original.roleSpan))+(last+1)*(3*layout.original.roleSpan)≤
      basePage+2*((last+1)*(3*layout.original.roleSpan))+(last+1)*(3*layout.original.roleSpan)+_+_+_
    omega
  have rankRoom : basePage<2^w := before.trans_lt ((Nat.le_add_right root _).trans_lt (endAt.trans_lt room))
  have fits:=v.wide_spill_role_fits h width ell unitCost v.maxBits first rom f t funded heap rankRoom strideFit
  have data:=v.wide_spill_role_observed h width size M π raw v.maxBits horizon age budget small operandAge
    issues card who cj marks unique A₀ first input m pages baseline keep cost highFit large rad floor accepted
    mounted rank heap paidAge ell unitCost rom strides f t
  obtain ⟨out,run,state,frame⟩:=sub.run_role rom root v.sampler π v.depth marks unique names qty id partialRow direction rfl
    m now t field basePage (before.trans (Nat.le_add_right ..)) fits data low (endAt.trans_lt room)
  exact ⟨out,run,state,fun a ha=>frame a (.inl ha)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
