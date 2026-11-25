import OAI.Hierarchy.TaggedWideRoleMaskSlots
import OAI.Hierarchy.ProbeFixedWideCorrectedDatesRun
import OAI.Hierarchy.TaggedWideSpillRetention

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
local notation "saved" => fun a=>v.wideBallotRows h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) a (entryMemory C mid a)

local notation "rr" => v.wideCorrectedRoleFact h width size M π raw issues marks unique ell unitCost first rom input
variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "rb" => fun processing : Memory w=>(∀a,a<startAt→processing a=m a) ∧ ∀i,(rr i).holds processing
local notation "br" => fun j=>v.wideSpillBallotFact h width ell unitCost bits first rom oldWork j saved rb
local notation "ready" => fun processing : Memory w=>rb processing ∧ ∀j,(br j).holds processing
local notation "fieldReport" => fun (b:Bool) (j:Fin last)=>
  v.wideCorrectedControlResult h width ell unitCost bits first rom oldWork startAt j b ready

local notation "retained" => fun (b:Bool) (j:Fin last)=>
  v.wideCorrectedControlRetained h width ell unitCost bits first rom oldWork startAt j b ready
local notation "keepControl" => wideCorrectedControlRetained.localize v h width ell unitCost bits first rom oldWork startAt

/-- The actual snapshots at which native ballot, port, and spill-control
fields were computed. The common rank-input tape for each date is preserved. -/
def correctedContents (out : Memory w) : Prop :=
  (∀i,(rr i).holds out) ∧ (∀j,(br j).holds out) ∧ (∀j,retained false j out) ∧ ∀j,retained true j out

theorem correctedContents.role {out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (f : Fin 3) (j : Fin (last+1)) (field : Fin 3) :
    DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart ((correct).roleRoot startAt f) j) (target f j ∘ embedded ∘ names)
      (fun i=>(sparse (names i)).val) out field := by
  have phys : ((correct).roles f).physical = oldRows := rfl
  have pos : ∀a,((correct).roles f).roleStart a j = (baseModel).roleStart a j := fun _ => rfl
  simpa only [wideCorrectedRoleFact,Equiv.symm_apply_apply,WideCPU.Dated.roleResult, phys, pos] using
    H.1 (finProdFinEquiv (f,finProdFinEquiv (j,field)))

/-- The intermediate active bitmap is read from the first native corrected
sheet of this execution, at the genuine party's physical shelf location. -/
theorem correctedContents.middle_cells {out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (j : Fin last) (capacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (fit : ∀i side,(target 0 j.succ ∘ embedded ∘ names) i≤capacity (named v.sampler π v.depth marks unique names (i,side)))
    (word : ∀party,capacity party<2^w) (q : (party : Public v.sampler h v.W k v.wideJobs)×Fin (capacity party)) :
    q∈Set.range (statePlace v.sampler π v.depth marks unique names (target 0 j.succ ∘ embedded ∘ names) capacity fit) ↔
    q.2.val<(out ((baseModel).roleStart ((correct).roleRoot startAt 0) j.succ+1+(shelfSlot v.sampler q.1).val)).val := by
  apply DatedRoleSheets.state_range v.sampler π v.depth marks unique names (target 0 j.succ ∘ embedded ∘ names)
    (fun i=>(sparse (names i)).val) capacity fit oldRows _ out (fun i=>(fit i false).trans_lt (word _))
    (correctedContents.role v h width size M π raw issues marks unique ell unitCost first rom oldWork input m H 0 j.succ 0) q

theorem correctedContents.middle_site {out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (j : Fin last) (capacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (fit : ∀i side,(target 0 j.succ ∘ embedded ∘ names) i≤capacity (named v.sampler π v.depth marks unique names (i,side)))
    (word : ∀party,capacity party<2^w) (cap : ℕ) (within : ∀party,capacity party≤cap)
    (s : Fin siteCount) (x : Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs*cap)) :
    (s,x)∈Set.range ((statePlace v.sampler π v.depth marks unique names (target 0 j.succ ∘ embedded ∘ names)
      capacity fit).trans (LedgerStep.rolesChart capacity within (shelfSlot v.sampler))) ↔
      (finProdFinEquiv.symm x).2.val<(out ((baseModel).roleStart ((correct).roleRoot startAt 0) j.succ+1+
        (finProdFinEquiv (s,(finProdFinEquiv.symm x).1)).val)).val :=
  DatedRoleSheets.dense_range v.sampler π v.depth marks unique names (target 0 j.succ ∘ embedded ∘ names)
    (fun i=>(sparse (names i)).val) capacity fit cap within (fun i=>(fit i false).trans_lt (word _))
    oldRows _ out (correctedContents.role v h width size M π raw issues marks unique ell unitCost first rom oldWork input m H 0 j.succ 0) s x

theorem correctedContents.control_prefix {out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (side : Bool) (j : Fin last) :
    let fields:=v.wideCorrectedControlFields h width ell unitCost bits first rom oldWork startAt j side
    let base:=v.wideCorrectedControlStart h width ell unitCost bits first startAt j side
    ∃before,(∀i,i<startAt→before i=m i) ∧ (∀i,(rr i).holds before) ∧ (∀i,(br i).holds before) ∧
      (∀addr,addr<base → out addr=before addr) ∧
      ∀partySite : Fin siteCount,∀c : Fin (SiteControls.fieldCount (HistoryRoles.stride k v.sampler.degree v.wideJobs)),
        out (base+1+(SiteScatter.pos partySite c).val)=(fields.value (0 : Fin 1) c).eval before (partySite.val:Word w) := by
  intro fields base
  have words : retained side j out := by cases side with
    | false=>exact H.2.2.1 j
    | true=>exact H.2.2.2 j
  obtain ⟨before,source,frame,native⟩:=words
  exact ⟨before,source.1.1,source.1.2,source.2,frame,native⟩

theorem correctedContents.control {out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (side : Bool) (j : Fin last) :
    let fields:=v.wideCorrectedControlFields h width ell unitCost bits first rom oldWork startAt j side
    let base:=v.wideCorrectedControlStart h width ell unitCost bits first startAt j side
    ∃before,(∀i,i<startAt→before i=m i) ∧ (∀i,(rr i).holds before) ∧ (∀i,(br i).holds before) ∧
      ∀partySite : Fin siteCount,∀c : Fin (SiteControls.fieldCount (HistoryRoles.stride k v.sampler.degree v.wideJobs)),
        out (base+1+(SiteScatter.pos partySite c).val)=(fields.value (0 : Fin 1) c).eval before (partySite.val:Word w) := by
  obtain ⟨before,low,roles,ballots,_,words⟩:=correctedContents.control_prefix v h width size M π raw issues marks unique
    ell unitCost first rom oldWork input m H side j
  exact ⟨before,low,roles,ballots,words⟩

theorem correctedContents.frame {early out : Memory w}
    (H : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m early)
    (low : ∀a,a<(correct).endAt startAt → out a=early a) :
    v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out :=
  (correct).results_prefix_below rom oldWork startAt (fun _=>rfl) (fun i=>(rr i).holds)
    (fun i=>(br i).holds) (retained false) (retained true)
    (fun i x y same=>(rr i).localize x y (fun a _ small=>same a small))
    (fun i x y same=>(br i).localize x y (fun a _ small=>same a small))
    (fun i=>keepControl i false ready) (fun i=>keepControl i true ready)
    early out low H.1 H.2.1 H.2.2.1 H.2.2.2
end Names

local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "region" => v.wideSpillPage h width bits first
local notation "tape" => v.wideSpillRanks h width bits first
local notation "required" => (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)
local notation "content" => v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork

include horizon age budget small operandAge card A₀
theorem wide_spill_rank_dates (initial : Memory w)
    (pages : v.WideDatedPages h width bits mid chk initial issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→initial x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (large : v.wideSpillSheetHeight≤h) (rad : M=v.radius)
    (floor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0)
    («directory» : ∃κ : Columns h D×Fin k→ℕ,RouteSettlement.Directory old initial ord PurchaseInventory.slot κ)
    (archiveFloor : required≤first) (headFloor : 6*2^page≤first) (funded : full≤first)
    (heap : (v.wideReserveLayout h width ss).scratch≤first)
    (paidAge : v.wideSpillPaidHeight≤h) (ballotAge : v.wideSpillBallotHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (top : (A).endAddress v.mesh≤rom)
    (transport : Fin rows→Bool) (romInput : Memory w)
    (header : ∀i,rom≤ i→i<(baseModel).romEnd rom→initial i=(baseModel).words rom (SiteDirectory.table h D k) transport romInput i)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (oldBefore : oldWork≤first)
    (room : (correct).endAt startAt<2^w) (wide : 2<2^w) :
    ∃ranked dated,(v.wideSpillRankProgram h width bits first).Exec initial ranked (v.wideSpillRankTicks h width bits first) ∧
      ((correct).program w rom oldWork startAt (fun _=>rfl)).Exec ranked dated ((correct).ticks rom oldWork startAt (fun _=>rfl)) ∧
      (∀a,a<startAt→dated a=ranked a) ∧ (∀a,a<first→ ranked a=initial a) ∧
      (∀j<last,DateSpill.RankTape.Observation tape mount o j initial ranked) ∧
      ∃inputs : Fin last→Memory w,(∀j,∀a,a<first→inputs j a=initial a) ∧
        (∀j,ProtocolRAMDateSpillRank.RankRead mount o (region j.val).rankStart (region j.val).overflow (inputs j) ranked) ∧
        content inputs ranked dated := by
  have firstFit : first ≤ startAt := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have rfit : startAt≤(correct).endAt startAt:=by
    dsimp only [SpillDates.endAt,SpillDates.roleRoot,Dated.maskStart,Dated.controlStart,Dated.rolesEnd,endOf];omega
  have arenaBound : (A).endAddress v.mesh ≤ first := (Nat.le_add_right ..).trans archiveFloor
  have romBound : (baseModel).romEnd rom ≤ first := by omega
  have wrd:=firstFit.trans_lt (rfit.trans_lt room)
  obtain ⟨ranked,run,frame,zero,obs⟩:=v.wide_spill_rank_run h width bits first π mount initial «directory»
    archiveFloor headFloor funded (rfit.trans_lt room) wide
  have each (j : Fin last):=DateSpill.RankTape.Observation.read tape mount o (obs j.val j.isLt) rfl
  choose inputs prep using each
  have source (j : Fin last) (a : ℕ) (low : a<(A).endAddress v.mesh) : inputs j a=chk a :=
    ((prep j).2.1 _ (low.trans_le arenaBound)).trans (stored _ low)
  have parent : ∀a,a<full→ ranked a=settled a:=fun i small=>(frame _ (small.trans_le funded)).trans (keep _ small)
  have ready:=v.wide_corrected_dates_retained h width size M π raw horizon age budget small operandAge issues card who cj marks
    unique A₀ ell unitCost first rom oldWork inputs ranked (pages.frame first heap wrd frame) baseline parent cost highFit large rad
    floor accepted source (fun j=>(prep j).1) heap (funded.trans firstFit) paidAge ballotAge
    (fun a ha=>(frame _ (ha.trans_le arenaBound)).trans (stored _ ha)) top transport romInput
    (fun a ha hb=>(frame _ (hb.trans_le romBound)).trans (header a ha hb)) gap (oldBefore.trans firstFit) room
  obtain ⟨dated,commit,rolesDone,ballotsDone,packetsDone,spillsDone,below⟩:=ready
  exact ⟨ranked,dated,run,commit,below,frame,obs,inputs,fun j=>(prep j).2.1,fun j=>(prep j).1,rolesDone,ballotsDone,packetsDone,spillsDone⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
