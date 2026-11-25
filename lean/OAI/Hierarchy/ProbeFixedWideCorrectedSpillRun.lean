import OAI.Hierarchy.ProbeFixedWideCorrectedSpillSource

namespace OAI
/-! # Return of the genuine post-pruning spill machine, including all dated outputs -/
noncomputable section
set_option quotPrecheck false
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


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H (WideMemory.R v.sampler h v.W k)
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H (WideMemory.R v.sampler h v.W k)
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

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
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "region" => v.wideSpillPage h width bits first
local notation "tape" => v.wideSpillRanks h width bits first
local notation "required" => (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)
local notation "content" => v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork

variable (terminalROM terminalWork : ℕ)
local notation "endDates" => (correct).endAt startAt
local notation "nt" => v.wideTerminal h width bits terminalROM terminalWork
local notation "parentB" => v.wideCorrectedSpillProgram h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "billed" => v.wideCorrectedSpillTicks h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "endAll" => v.wideCorrectedSpillEnd h width ell unitCost bits rom oldWork terminalROM terminalWork first
local notation "pre" => (correct).preClip oldWork startAt
local notation "post" => fun j=>(baseModel).roleStart oldWork j.succ
local notation "lo" => fun j=>(correct).dateRole startAt j 1
local notation "hiRole" => fun j=>(correct).dateRole startAt j 2
local notation "panel" => v.wideSpillTurnPage h width bits rom terminalROM terminalWork first endDates pre post lo hiRole
local notation "Seat" => ProtocolRAMTurnShelf.Seats (nt).sites (nt).seats
local notation "G" => fun (m : Memory w)=>∀j : Fin last,(panel j).Inputs endDates m

local notation "board" => v.wideTerminalBoard h width bits terminalWork
local notation "stageExtent" => (board).endAt+3*(board).old
local notation "pubPort" => Public v.sampler h v.W k v.wideJobs
local notation "heads" => fun e (on : 0<counts e) side=>
  (Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side)):pubPort)

local notation "funding" => v.FundedTurnSource h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork
local notation "fromArchive" => v.nativeTurnSources h width size M π raw first
include horizon age budget small operandAge card marks unique A₀
theorem wide_corrected_spill_run (initial : Memory w)
    (pages : v.WideDatedPages h width bits mid chk initial issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→initial x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (shape).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    («directory» : ∃κ : Columns h D×Fin k→ℕ,RouteSettlement.Directory old initial ord PurchaseInventory.slot κ)
    (archiveFloor : required≤first) (headFloor : 6*2^page≤first) (funded : full≤first)
    (heap : (v.wideReserveLayout h width ss).scratch≤first)
    (paidAge : v.wideSpillPaidHeight≤h) (ballotAge : v.wideSpillBallotHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (top : (A).endAddress v.mesh≤rom)
    (transport : Fin rows→Bool) (romInput : Memory w)
    (header : ∀i,rom ≤ i → i < (baseModel).romEnd rom→initial i=(baseModel).words rom (SiteDirectory.table h D k) transport romInput i)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (oldBefore : oldWork≤first)
    (room : (correct).endAt startAt<2^w) (wide : 2<2^w)
    (endRoom : endAll≤2^w)
    (funds : funding initial)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first) :
    let authentic:=(fun (sch:Memory w) (choice:fromArchive initial sch)=>
      v.fundedSpillAccess h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
        ell unitCost first rom oldWork terminalROM terminalWork initial sch funds choice baseline bought cost rad paidAge
        stored keep readOnly replayed terminalFloor funded oldBefore gap room)
    ∃out,(parentB).Exec initial out billed ∧ (∀a,a<first → out a=initial a) ∧
      ∃ ranked sch inputs, ∃ chartState : fromArchive initial sch,
        (∀a,a<first→ ranked a=initial a) ∧ (∀a,a < startAt → sch a=ranked a) ∧
        (∀a,a<endDates → out a=sch a) ∧ (∀j<last,DateSpill.RankTape.Observation tape mount o j initial ranked) ∧
        (∀j,∀a,a<first→inputs j a=initial a) ∧ content inputs ranked out ∧
        ∀j (f : Fin 5) (seat : Seat),out ((panel j).base+f.val*((nt).sites*(nt).seats)+seat.1.val*(nt).seats+seat.2.val)=
          (authentic sch chartState j).word f seat := by
  intro authentic
  let provenance (sch : Memory w) (access : G sch) := ∃receipt : fromArchive initial sch,access=authentic sch receipt
  have all:=v.wide_spill_return h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial pages baseline keep cost highFit large rad floor accepted
    «directory» archiveFloor headFloor funded heap paidAge ballotAge stored top transport romInput header gap oldBefore room
    wide endRoom provenance (fun ranked sch inputs prior later obs low core state=>by
      have firstFit : first ≤ startAt:=by change first≤first+_+_;omega
      have hold : fromArchive initial sch:=by
        refine ⟨fun a h=>(later _ (h.trans_le firstFit)).trans (prior _ h),?_⟩
        intro j hj
        obtain ⟨savedInput,marker,got,readSource,values,frozen⟩:=(obs j hj).stored
        refine ⟨savedInput,marker,got,readSource,values,fun a belowPage=>(later _ (belowPage.trans_le (v.wide_spill_rank_page_end h width bits first ⟨j,hj⟩))).trans (frozen _ belowPage)⟩
      exact ⟨authentic sch hold,hold,rfl⟩)
  obtain ⟨out,run,low,ranked,sch,inputs,access,⟨origin,identity⟩,prior,localReads,below,ranks,oldQ,dates,turns⟩:=all
  subst access
  exact ⟨out,run,low,ranked,sch,inputs,origin,prior,localReads,below,ranks,oldQ,dates,turns⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
