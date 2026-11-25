import OAI.Hierarchy.ProbeFixedWideSpillRolePages
import OAI.Hierarchy.ProbeFixedWideCorrectedControl
import OAI.Hierarchy.ProbeFixedWideSpillBallotSteps
import OAI.Hierarchy.TaggedWideSpillAfterRoles
import OAI.Hierarchy.TaggedWideSparsePrefixImage

namespace OAI
/-! # One actual execution for all corrected role, ballot and local comparison fields -/
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
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
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
variable (ell unitCost first rom oldWork : ℕ) (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "target" => v.wideCorrectedWidths h width size M π raw bits issues first input
local notation "region" => v.wideSpillPage h width bits first
local notation "saved" => fun a=>v.wideBallotRows h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) a (entryMemory C mid a)

def wideCorrectedRoleFact (l : Fin (3*((last+1)*3))) : PageResult w ((correct).roleSheet rom startAt l) :=
  let b : Fin 3×Fin ((last+1)*3):=finProdFinEquiv.symm l
  let t : Fin (last+1)×Fin 3:=finProdFinEquiv.symm b.2
  let rr:=(correct).roles b.1
  rr.roleResult rom ((correct).roleRoot startAt b.1) v.sampler π v.depth marks unique names
    (fun j=>target b.1 j ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) rfl t.1 t.2

local notation "rr" => v.wideCorrectedRoleFact h width size M π raw issues marks unique ell unitCost first rom input
variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "rb" => fun processing : Memory w=>(∀a,a<startAt→processing a=m a) ∧ ∀i,(rr i).holds processing
local notation "br" => fun j=>v.wideSpillBallotFact h width ell unitCost bits first rom oldWork j saved rb
local notation "ready" => fun processing : Memory w=>rb processing ∧ ∀j,(br j).holds processing
local notation "fieldReport" => fun (b:Bool) (j:Fin last)=>
  v.wideCorrectedControlResult h width ell unitCost bits first rom oldWork startAt j b ready

def wideSpillBallotHeight := Nat.find (Filter.eventually_atTop.1 v.wide_spill_ballot_steps)

local notation "retained" => fun (b:Bool) (j:Fin last)=>
  v.wideCorrectedControlRetained h width ell unitCost bits first rom oldWork startAt j b ready
local notation "keepControl" => wideCorrectedControlRetained.localize v h width ell unitCost bits first rom oldWork startAt

include horizon age budget small operandAge card A₀
theorem wide_corrected_dates_retained
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    (mounted : ∀j,∀x<(A).endAddress v.mesh,input j x=chk x)
    (rank : ∀j : Fin last,ProtocolRAMDateSpillRank.RankRead mount o (region j.val).rankStart
      (region j.val).overflow (input j) m)
    (heap : (v.wideReserveLayout h width ss).scratch≤first) (funded : full≤ startAt)
    (paidAge : v.wideSpillPaidHeight≤h) (ballotAge : v.wideSpillBallotHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→m i=chk i) (top : (A).endAddress v.mesh≤rom)
    (transport : Fin rows→Bool) (romInput : Memory w)
    (header : ∀i,rom≤ i→i<(baseModel).romEnd rom→m i=(baseModel).words rom (SiteDirectory.table h D k) transport romInput i)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (below : oldWork≤ startAt) (room : (correct).endAt startAt<2^w) :
    ∃out,((correct).program w rom oldWork startAt (fun _=>rfl)).Exec m out ((correct).ticks rom oldWork startAt (fun _=>rfl)) ∧
      (∀i,(rr i).holds out) ∧ (∀j,(br j).holds out) ∧ (∀j,retained false j out) ∧
      (∀j,retained true j out) ∧ ∀a,a<startAt → out a=m a := by
  have image:=(baseModel).mounted_image rom (SiteDirectory.table h D k) transport romInput m header
  have floorEnd : startAt≤(correct).endAt startAt:=by
    dsimp only [SpillDates.endAt,Dated.maskStart,Dated.controlStart,Dated.rolesEnd,SpillDates.roleRoot,endOf];omega
  have word := floorEnd.trans_lt room
  have beforeSite : rom+(baseModel).sites≤(baseModel).romEnd rom:=by
    dsimp only [Dated.romEnd,Dated.maskROM,Dated.controlROMStart,Dated.firstROM,Dated.siteROM,endOf];omega
  have bank:=((baseModel).global_banks ((gap.trans below)) word).2
  have sizes:(baseModel).sites=siteCount:=rfl
  have slots:=ProtocolRAMPurchaseSampler.span_le siteCount
  have siteFit : rom+ProtocolRAMPurchaseSampler.span siteCount≤ startAt:=by omega
  have strides (x:Fin siteCount) : ((baseModel).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w) := by
    have h:=(baseModel).stride_mounted rom (SiteDirectory.table h D k) transport m x
    rw [image] at h
    change m (rom+(x.val:Word w).val%ProtocolRAMPurchaseSampler.span siteCount)=_
    rw [Fin.val_cast_of_lt (by have:=x.isLt;omega),Nat.mod_eq_of_lt (x.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
    exact h
  apply (correct).run_after_roles_prefix rom oldWork startAt (fun _=>rfl) m (fun i=>(rr i).holds)
    (fun i=>(br i).holds) (retained false) (retained true)
    (fun i x y same=>(rr i).localize x y (fun a _ small=>same a small))
    (fun i x y same=>(br i).localize x y (fun a _ small=>same a small))
    (fun i=>keepControl i false ready) (fun i=>keepControl i true ready)
  · intro i now earlier _
    let block : Fin 3 × Fin ((last+1)*3) := finProdFinEquiv.symm i
    let date : Fin (last+1) × Fin 3 := finProdFinEquiv.symm block.2
    exact v.wide_spill_role_issued h width size M π raw bits horizon age budget small operandAge issues card who cj
      marks unique A₀ first input m pages baseline keep cost highFit large rad floor accepted mounted rank heap
      paidAge ell unitCost rom strides funded siteFit rfl room block.1 date.1 date.2 now earlier
  · have instanceRun:=(Nat.find_spec (Filter.eventually_atTop.1 v.wide_spill_ballot_steps)) h ballotAge width small budget
      size ((v.wide_funded_extent h width bits).trans horizon) M π seed rad ell unitCost bits first rom oldWork
      transport m stored top gap below room rb
    rw [image] at instanceRun
    intro j processing baseState prev
    exact instanceRun j processing ⟨baseState.1,baseState⟩ prev
  · intro j source retainedBase earlier
    apply v.wide_corrected_control_retained_step h width ell unitCost bits first rom oldWork startAt j false ready source
      retainedBase (SiteDirectory.table h D k) transport romInput _ below gap room
    intro i lower upper
    have e:=extent ((baseModel).controlROMStart rom) (fun t=>((baseModel).control t).advice (baseModel).sites) j
    change (baseModel).controlROM rom j+_≤(baseModel).maskROM rom at e
    have loROM : rom≤(baseModel).controlROM rom j:=by
      dsimp only [Dated.controlROM,Dated.controlROMStart,Dated.firstROM,Dated.siteROM,endOf,WideCPU.offset];omega
    have topROM : (baseModel).maskROM rom≤(baseModel).romEnd rom:=Nat.le_add_right ..
    exact (retainedBase.1.1 _ (by omega)).trans (header _ (by omega) (by omega))
  · intro j source extra earlier
    have retainedBase:=extra.1
    apply v.wide_corrected_control_retained_step h width ell unitCost bits first rom oldWork startAt j true ready source
      retainedBase (SiteDirectory.table h D k) transport romInput _ below gap room
    intro i lower upper
    have e:=extent ((baseModel).controlROMStart rom) (fun t=>((baseModel).control t).advice (baseModel).sites) j
    change (baseModel).controlROM rom j+_≤(baseModel).maskROM rom at e
    have loROM : rom≤(baseModel).controlROM rom j:=by
      dsimp only [Dated.controlROM,Dated.controlROMStart,Dated.firstROM,Dated.siteROM,endOf,WideCPU.offset];omega
    have topROM : (baseModel).maskROM rom≤(baseModel).romEnd rom:=Nat.le_add_right ..
    exact (retainedBase.1.1 _ (by omega)).trans (header _ (by omega) (by omega))

include horizon age budget small operandAge card A₀
theorem wide_corrected_dates_run
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    (mounted : ∀j,∀x<(A).endAddress v.mesh,input j x=chk x)
    (rank : ∀j : Fin last,ProtocolRAMDateSpillRank.RankRead mount o (region j.val).rankStart
      (region j.val).overflow (input j) m)
    (heap : (v.wideReserveLayout h width ss).scratch≤first) (funded : full≤ startAt)
    (paidAge : v.wideSpillPaidHeight≤h) (ballotAge : v.wideSpillBallotHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→m i=chk i) (top : (A).endAddress v.mesh≤rom)
    (transport : Fin rows→Bool) (romInput : Memory w)
    (header : ∀i,rom≤ i→i<(baseModel).romEnd rom→m i=(baseModel).words rom (SiteDirectory.table h D k) transport romInput i)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (below : oldWork≤ startAt) (room : (correct).endAt startAt<2^w) :
    ∃out,((correct).program w rom oldWork startAt (fun _=>rfl)).Exec m out ((correct).ticks rom oldWork startAt (fun _=>rfl)) ∧
      (∀i,(rr i).holds out) ∧ (∀j,(br j).holds out) ∧ (∀j,(fieldReport false j).holds out) ∧
      (∀j,(fieldReport true j).holds out) ∧ ∀a,a<startAt → out a=m a := by
  obtain ⟨out,run,roles,ballots,packets,spills,frame⟩:=v.wide_corrected_dates_retained h width size M π raw
    horizon age budget small operandAge issues card who cj marks unique A₀ ell unitCost first rom oldWork
    input m pages baseline keep cost highFit large rad floor accepted mounted rank heap funded paidAge ballotAge
    stored top transport romInput header gap below room
  refine ⟨out,run,roles,ballots,fun j=>?_,fun j=>?_,frame⟩
  · obtain ⟨before,prior,_,words⟩:=packets j
    exact ⟨before,prior,words⟩
  · obtain ⟨before,prior,_,words⟩:=spills j
    exact ⟨before,prior,words⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
