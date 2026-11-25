import OAI.Hierarchy.ProbeFixedWideSpillReturn
import OAI.Hierarchy.ProbeFixedWideSpillFundedChart
import OAI.Hierarchy.ProbeFixedWideEarlyBanks

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

def nativeTurnSources (initial sch : Memory w) : Prop :=
  (∀a,a<first→sch a=initial a) ∧ ∀j<last,DateSpill.RankTape.Observation tape mount o j initial sch

private structure TurnSourceConditions where
  State : Type
  Slot : Type
  Port : Type
  kept : State → Prop
  archived : State → Prop
  read : (amount : Slot → ℕ) → (∀i, 0 < amount i → Bool → Port) → Prop
  hasHeader : State → Prop

private def turnSourceConditions (initial : Memory w) : TurnSourceConditions where
  State := Memory w
  Slot := Fin (board).old
  Port := pubPort
  kept before := ∀a<full, before a = settled a
  archived before := ∀a<stageExtent, initial a = (board).extendedState (nt).stock before a
  read amount portAt := (board).LiveReads v.sampler amount counts portAt heads initial
  hasHeader romSeed := ∀a, terminalROM ≤ a → a < v.wideTerminalROMEnd h width bits terminalROM terminalWork →
    initial a = v.wideTerminalWords h width bits terminalROM terminalWork romSeed a

private structure TurnSourceEvidence (conditions : TurnSourceConditions) where
  before : conditions.State
  romSeed : conditions.State
  beforeLow : conditions.kept before
  «archive» : conditions.archived before
  amount : conditions.Slot → ℕ
  portAt : ∀i, 0 < amount i → Bool → conditions.Port
  seen : conditions.read amount portAt
  header : conditions.hasHeader romSeed

attribute [reducible] turnSourceConditions
local notation "sourceConditions" => turnSourceConditions v h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork

/-- The complete original turnover source is a concrete allocation, including
the archived endpoint words of rows whose current amount has dropped to zero. -/
abbrev FundedTurnSource (initial : Memory w) : Type := TurnSourceEvidence (sourceConditions initial)

namespace FundedTurnSource
variable {v h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork}
    {initial : Memory (Native.wordBits h (2 ^ v.W) Native.copies)}
    (witness : v.FundedTurnSource h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork initial)
abbrev mk := @TurnSourceEvidence.mk (sourceConditions initial)
abbrev rec := @TurnSourceEvidence.rec (sourceConditions initial)
abbrev casesOn := @TurnSourceEvidence.casesOn (sourceConditions initial)
abbrev before := TurnSourceEvidence.before witness
abbrev romSeed := TurnSourceEvidence.romSeed witness
abbrev beforeLow := TurnSourceEvidence.beforeLow witness
abbrev «archive» := TurnSourceEvidence.archive witness
abbrev amount := TurnSourceEvidence.amount witness
abbrev portAt := TurnSourceEvidence.portAt witness
abbrev seen := TurnSourceEvidence.seen witness
abbrev header := TurnSourceEvidence.header witness
end FundedTurnSource


local notation "funding" => v.FundedTurnSource h width size M π raw issues who cj marks unique A₀ terminalROM terminalWork
local notation "fromArchive" => v.nativeTurnSources h width size M π raw first
local notation "baseChord" => publicChord h D k

def MountedSpillFields (j : Fin last) (initial sch : Memory w) (R : (panel j).Inputs endDates sch) : Prop :=
    let keep:=ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
    let selected:=R.columns ∘ keep
    let seats:=(ProtocolRAMTurnShelf.restrictedLive R.columns keep).trans R.put
    ((∀f a,R.word f a=ProtocolRAMTurnShelf.entry selected seats f a) ∧
      ∀i : ProtocolRAMTurnShelf.Live selected,(seats i).1.val=
      ((ProtocolRAMDateSpillPosition.sparseSpine v.sampler π mount baseChord
        (((mount).datedLayout (siteNumber h D k).injective baseChord).num
          (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).1)).visit
        (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).2).val) ∧
    ∀i,R.columns (keep i) 4=((mount).datedLayout (siteNumber h D k).injective baseChord).bits
      (fun good=>RouteSettlement.actual (v.wideSpillPage h width bits first j.val).overflow initial (PurchaseInventory.slot good))
      (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i).1

include horizon age budget small operandAge card marks unique A₀
omit horizon age budget small operandAge card in
theorem fundedSpillAccess_operands (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (_baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (_bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (_cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (_rad : M=v.radius) (_paidAge : v.wideSpillPaidHeight≤h)
    (_stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (_keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (_replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last) : (board).LiveReads v.sampler funds.amount counts funds.portAt heads sch ∧
      (∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM terminalWork→
        sch a=v.wideTerminalWords h width bits terminalROM terminalWork funds.romSeed a) ∧
      stageExtent≤first ∧ (v.wideSpillPage h width bits first j.val).offsetsStart≤endDates ∧ first≤endDates ∧
      (panel j).left.prefix.Fits w endDates ∧ (panel j).right.prefix.Fits w endDates := by
  have rf : first≤ startAt:=by change first≤first+_+_;omega
  let root:=(correct).roleRoot startAt 2
  have rootStart : startAt≤root:=Nat.le_add_right ..
  have upto : ((baseModel).controlBase root j)+1≤endDates:=by
    have e:=extent ((baseModel).controlStart root) (fun j=>((baseModel).control j).span (baseModel).sites) j
    change (baseModel).controlBase root j+((baseModel).control j).span (baseModel).sites≤(baseModel).maskStart root at e
    have fee : (baseModel).maskStart root≤endDates:=Nat.le_add_right ..
    simp only [WideCPU.Shape.span] at e;omega
  have dfit : first≤endDates:=by
    have h:root≤(baseModel).rolesEnd root:=Nat.le_add_right ..
    have b:(baseModel).rolesEnd root≤(baseModel).controlStart root:=Nat.le_add_right ..
    have c:(baseModel).controlStart root≤(baseModel).controlBase root j:=Nat.le_add_right ..
    omega
  obtain ⟨wBoard,maxBoard,rankFloor,floorEnd,origRoom,edgeRoom⟩:=v.wide_terminal_role_floors h width bits terminalWork
    (terminalFloor.trans (dfit.trans room.le))
  have stamped : stageExtent≤first:=maxBoard.trans (rankFloor.trans (floorEnd.trans terminalFloor))
  have retained := Board.LiveReads.frame (S := v.sampler) (b := board) funds.seen first stamped origRoom edgeRoom actual.1
  have romBefore : rom+(baseModel).sites≤(baseModel).romEnd rom:=by
    dsimp only [Dated.romEnd,Dated.maskROM,Dated.controlROMStart,Dated.firstROM,Dated.siteROM,endOf];omega
  have strideBound : rom+ProtocolRAMPurchaseSampler.span siteCount≤endDates:=by
    have hs : (baseModel).sites=siteCount:=rfl
    have hp:=ProtocolRAMPurchaseSampler.span_le siteCount;omega
  have pair:=v.wide_spill_offset_stage_fits h width ell unitCost rom oldWork terminalROM terminalWork first j
    (oldBefore.trans rf) room (funded.trans dfit) (terminalFloor.trans dfit) strideBound
  have frozen : ∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM terminalWork→
      sch a=v.wideTerminalWords h width bits terminalROM terminalWork funds.romSeed a := by
    intro a lower upper
    have workEndBound : terminalWork≤v.wideTerminalWorkEnd h width bits terminalWork:=
      wBoard.trans ((Nat.le_add_right _ _).trans (maxBoard.trans (rankFloor.trans floorEnd)))
    exact (actual.1 _ (upper.trans_le (readOnly.trans (workEndBound.trans terminalFloor)))).trans (funds.header _ lower upper)
  have position : (v.wideSpillPage h width bits first j.val).offsetsStart≤endDates :=
    ((v.wide_spill_rank_page_end h width bits first j).trans (rootStart.trans (by
      have h0: root≤(baseModel).rolesEnd root:=Nat.le_add_right ..
      have h1:(baseModel).rolesEnd root≤(baseModel).controlStart root:=Nat.le_add_right ..
      have h2:(baseModel).controlStart root≤(baseModel).controlBase root j:=Nat.le_add_right ..
      omega)))
  exact ⟨retained,frozen,stamped,position,dfit,pair⟩

private def spillAccessMarked (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last) : {R : (panel j).Inputs endDates sch // MountedSpillFields v h width size M π raw ell unitCost first rom oldWork terminalROM terminalWork j initial sch R} := by
  have evidence:=v.fundedSpillAccess_operands h width size M π raw issues who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
    stored keep readOnly replayed terminalFloor funded oldBefore gap room j
  let retained:=evidence.1
  let frozen:=evidence.2.1
  let stamped:=evidence.2.2.1
  let position:=evidence.2.2.2.1
  let dfit:=evidence.2.2.2.2.1
  let pair:=evidence.2.2.2.2.2
  exact ⟨v.wide_spill_turn_funded_chart h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ rom terminalROM terminalWork first endDates pre post lo hiRole j funds.before initial sch funds.romSeed
    baseline bought cost rad paidAge stored funds.beforeLow keep funds.archive (actual.2 _ j.isLt)
    funds.amount funds.portAt retained frozen readOnly replayed stamped (terminalFloor.trans dfit)
    position dfit room pair.1 pair.2,
    v.wide_spill_turn_funded_chart_word h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ rom terminalROM terminalWork first endDates pre post lo hiRole j funds.before initial sch funds.romSeed
    baseline bought cost rad paidAge stored funds.beforeLow keep funds.archive (actual.2 _ j.isLt)
    funds.amount funds.portAt retained frozen readOnly replayed stamped (terminalFloor.trans dfit)
    position dfit room pair.1 pair.2,
    v.wide_spill_turn_funded_widths h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ rom terminalROM terminalWork first endDates pre post lo hiRole j funds.before initial sch funds.romSeed
    baseline bought cost rad paidAge stored funds.beforeLow keep funds.archive (actual.2 _ j.isLt)
    funds.amount funds.portAt retained frozen readOnly replayed stamped (terminalFloor.trans dfit)
    position dfit room pair.1 pair.2⟩

def fundedSpillAccess (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last) : (panel j).Inputs endDates sch :=
  (v.spillAccessMarked h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
    stored keep readOnly replayed terminalFloor funded oldBefore gap room j).1

theorem fundedSpillAccess_replay (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last) :
    let evidence := v.fundedSpillAccess_operands h width size M π raw issues who cj marks unique A₀
      ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
      stored keep readOnly replayed terminalFloor funded oldBefore gap room j
    v.fundedSpillAccess h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
      ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
      stored keep readOnly replayed terminalFloor funded oldBefore gap room j =
      v.wide_spill_turn_funded_chart h width size M π raw bits horizon age budget small operandAge issues card who cj
        marks unique A₀ rom terminalROM terminalWork first endDates pre post lo hiRole j funds.before initial sch funds.romSeed
        baseline bought cost rad paidAge stored funds.beforeLow keep funds.archive (actual.2 _ j.isLt)
        funds.amount funds.portAt evidence.1 evidence.2.1 readOnly replayed evidence.2.2.1 (terminalFloor.trans evidence.2.2.2.2.1)
        evidence.2.2.2.1 evidence.2.2.2.2.1 room evidence.2.2.2.2.2.1 evidence.2.2.2.2.2.2 := rfl

theorem fundedSpillAccess_fields (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last) : MountedSpillFields v h width size M π raw ell unitCost first rom oldWork terminalROM terminalWork j initial sch
      (v.fundedSpillAccess h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
    stored keep readOnly replayed terminalFloor funded oldBefore gap room j) :=
  (v.spillAccessMarked h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
    stored keep readOnly replayed terminalFloor funded oldBefore gap room j).2

theorem fundedSpillAccess_columns (initial sch : Memory w) (funds : funding initial) (actual : fromArchive initial sch)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (bought : ∀z : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex z))
      ((P).catalogue.bought.view chk (z.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex z).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (stored : ∀i,i<(A).endAddress v.mesh→initial i=chk i) (keep : ∀x,x<full→initial x=settled x)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (replayed : v.wideReplayedTurnBase h width ss≤terminalWork)
    (terminalFloor : v.wideTerminalWorkEnd h width bits terminalWork≤first)
    (funded : full≤first) (oldBefore : oldWork≤first)
    (gap : 3*(baseModel).romEnd rom+2≤oldWork) (room : endDates<2^w)
    (j : Fin last)
    (i : Fin (nt).turns) :
    let R:=(v.fundedSpillAccess h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM terminalWork initial sch funds actual baseline bought cost rad paidAge
    stored keep readOnly replayed terminalFloor funded oldBefore gap room j)
    let decode:=(ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
    let len := ProtocolRAMTurnGeometry.length (h:=h) (d:=D) (k:=k) (edges:=rows) ∘ decode
    let vis:=ProtocolRAMVisitAdjacency.vertex len
      (fun a=>ProtocolRAMTurnEdges.visit mount (siteNumber h D k).injective baseChord (decode a))
    let u:=ProtocolRAMTurnGeometry.header o (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler) decode
    R.columns i=DateSpill.Turns.fieldWords (ProtocolRAMTurnChart.record u (ProtocolRAMTurnChart.captured (panel j).data sch) vis i)
      (ProtocolRAMTurnSnapshot.values (panel j).banks sch) (fun n=>((panel j).left.prefix.eval sch (n:Word w)).val)
      (fun n=>((panel j).right.prefix.eval sch (n:Word w)).val) := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
