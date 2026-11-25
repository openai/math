import OAI.Hierarchy.ProbeFixedWideSpillTurnActive
import OAI.Hierarchy.ProbeFixedWideSpillPooledChart
import OAI.Hierarchy.TaggedWideSpillPooledRoles
import OAI.Hierarchy.ProtocolRAMDateSpillObservation
import OAI.Hierarchy.ProbeFixedWideSpillOnlySheets
import OAI.Hierarchy.ProbeFixedWideSpillOffsetFits
import OAI.Hierarchy.ProtocolRAMDateSpillPaidHalves
import OAI.Hierarchy.TaggedWireMountedChord

namespace OAI
/-! # The funded original RAM produces an executable chart at each earlier spill date -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
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
local notation "geometrySource" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) geometrySource v.sampler h v.W k v.wideJobs
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
local notation "last" => (events v.mesh).length

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

include horizon age budget small operandAge card


open DateSpill ProtocolRAMDateSpillRank ProtocolRAMTurnChart ProtocolRAMTurnSnapshot
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open CoreBoard.WordSeats
include marks unique A₀
variable (datedROM terminalROM work rankFirst turnFirst : ℕ)
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ) (j : Fin (events v.mesh).length)
local notation "panel" => v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
  oldStart newStart leftOnly rightOnly j
local notation "ranker" => v.wideSpillRanks h width bits rankFirst
local notation "rpage" => v.wideSpillPage h width bits rankFirst j.val
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "stk" => v.wideTerminalStock h width bits
local notation "extent₀" => (tr).endAt+3*oldRows
local notation "slotRoom" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "RawOld" => ProtocolRAMTurnGeometry.Source rows h D k
local notation "decode" => (ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
local notation "encode" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "chart" => captured (panel).data

local notation "win" => v.wideTurnWindow h width bits work
local notation "T" => v.wideTerminal h width bits terminalROM work
local notation "baseChord" => publicChord h D k
local notation "Port" => Public v.sampler h v.W k v.wideJobs


omit operandAge marks unique A₀ in
/-- The complete dated weight column follows the executed rank pass, even when a
goods row happens to be zero. -/
theorem wide_spill_turn_goods_width (rankedInput output : Memory w)
    (kept : ∀x<full,rankedInput x=settled x)
    (observed : RankTape.Observation ranker mount o j.val rankedInput output)
    (smallRows : oldRows≤2^w) (item : Goods h v.W k) :
    (chart output).width ((encode) (.inr (.inl item))).val=
      RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot item) := by
  let a : Fin oldRows:=encode (.inr (.inl item))
  have key : (decode) a=.inr (.inl item):=(encode).symm_apply_apply _
  have fromArchive:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small
    (entries:=recordCount v.mesh issues) card who dur
    (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k)
    (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun x=>(cj x).val) rankedInput kept
  have tag:=DatedRoleInput.decoded ((z).stop hi) rankedInput ((lw).bank last) stock (old).reserved (old).used
    fromArchive.2.2.1 smallRows a
  change (stk).kind.eval rankedInput (a.val:Word w)=(DatedRoleInput.tag ((decode) a):Word w) ∧
    (stk).index.eval rankedInput (a.val:Word w)=(DatedRoleInput.localIndex ((decode) a):Word w) at tag
  have kind : (stk).kind.eval rankedInput (a.val:Word w)=(1:Word w):=tag.1.trans
    (congrArg (fun y=>((DatedRoleInput.tag y:ℕ):Word w)) key)
  have index : (stk).index.eval rankedInput (a.val:Word w)=(PurchaseInventory.slot item:Word w):=tag.2.trans
    (congrArg (fun y=>((DatedRoleInput.localIndex y:ℕ):Word w)) key)
  obtain ⟨before,rank,_,amount⟩:=RankTape.Observation.read ranker mount o observed rfl
  have stored : (rpage).amount.read output (a.val:Word w)=((rpage).term (stk).kind (stk).index).eval rankedInput (a.val:Word w) := by
    have cap : oldRows≤(rpage).amount.size:=(rpage).amount_room
    change output ((rpage).amount.base+(a.val:Word w).val%(rpage).amount.size)=_
    rw [Fin.val_cast_of_lt (a.isLt.trans_le smallRows),Nat.mod_eq_of_lt (a.isLt.trans_le cap)]
    exact (rank.frame _ (Nat.add_lt_add_left (a.isLt.trans_le cap) _)).trans (amount a)
  apply congrArg Fin.val
  change (rpage).amount.read output (a.val:Word w)=_
  simpa [Page.term,Expr.eval,kind,index,DescriptorExpr.Comparison.test] using stored



omit horizon age budget small operandAge card marks unique A₀ in
/-- The same two paid workspaces that perform the original terminal and dated
rank executions cover all untruncated role, rank-offset, and edge identifiers. -/
theorem wide_spill_turn_field_room
    (oldWindow : v.wideTerminalWorkEnd h width bits work≤turnFirst)
    (rankWindow : (rpage).offsetsStart≤turnFirst) (word : turnFirst<2^w) :
    2*slotRoom≤2^w ∧ rows≤2^w ∧ 4*(rows+coreCount o)≤2^w ∧
      (∀e : Fin rows,counts e<2^w) := by
  obtain ⟨_,_,_,shelf,finish⟩ := (win).bounds
  have cap : (win).stop ≤ 2^w := oldWindow.trans word.le
  have enough : slotRoom ≤ (win).sites*(win).seats :=
    (Nat.le_add_right slotRoom (1+9*k)).trans
      (Nat.le_mul_of_pos_left (win).seats (Nat.succ_pos _))
  have doubled : 2*slotRoom ≤ 5*((win).sites*(win).seats) :=
    Nat.mul_le_mul (by decide) enough
  have shelfFit : 2*slotRoom ≤ 2^w :=
    doubled.trans ((Nat.le_add_left _ _).trans (shelf.trans
      ((Nat.le_add_right _ _).trans (finish.le.trans cap))))
  have rank := ProtocolRAMTurnReplayed.rank_room (rpage).rankStart (rows+coreCount o) rows
  have endRank : ProtocolRAMTurnReplayed.endAt (rpage).rankStart (rows+coreCount o) rows ≤ turnFirst :=
    (Nat.le_add_right ..).trans rankWindow
  have four : 4*(rows+coreCount o) ≤ 2^w :=
    (Nat.le_add_left _ _).trans (rank.trans (endRank.trans word.le))
  exact ⟨shelfFit, (Nat.le_add_right rows (coreCount o)).trans
    ((Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans four),
    four, fun _ => Fin.isLt _⟩



omit horizon age budget small operandAge card marks unique A₀ in
/-- A single retained replay observation exposes the real rank and all the original
overflow words fed to that rank, discharging its masked-bank bound in this chart. -/
theorem wide_spill_turn_rank_origin (rankedInput output : Memory w)
    (observed : RankTape.Observation ranker mount o j.val rankedInput output)
    (heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)≤rankFirst)
    (word : rankFirst<2^w) :
    ∃origin,ProtocolRAMDateSpillRank.RankRead mount o (rpage).rankStart (rpage).overflow origin output ∧
      ∀i,RouteSettlement.actual (rpage).overflow origin i=RouteSettlement.actual (rpage).overflow rankedInput i := by
  have endOfRows:=v.wide_spill_page_floor h width bits rankFirst j heap
  have fits : (rpage).overflow.Fits w rankFirst :=
    ⟨Nat.two_pow_pos _,Nat.lt_of_le_of_lt ((Nat.le_add_left _ _).trans endOfRows) word,endOfRows⟩
  obtain ⟨origin,rank,amount,_,_⟩:=RankTape.Observation.read_overflow observed rfl fits
  exact ⟨origin,rank,amount⟩



/-- The real rank memory contains both original signed endpoint codes. This
uses the pre-rank role archive on every historical commodity, including one
whose stock later runs out. -/
theorem wide_spill_turn_original_words (initial rankedInput output : Memory w)
    (initialLow : ∀x<full,initial x=settled x)
    (frozen : ∀x<extent₀,rankedInput x=(tr).extendedState stk initial x)
    (observed : RankTape.Observation ranker mount o j.val rankedInput output)
    (replayed : v.wideReplayedTurnBase h width ss≤work) (within : extent₀≤rankFirst)
    (native : rankFirst<2^w)
    (sites : siteLast h D k+1≤2^w) (good : Goods h v.W k) :
    let i:=(encode) (.inr (.inl good))
    let p:=publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr (.inl good))
    ∀side,((tr).forwardSite side).read output (i.val:Word w)=((name (HistoryRoles.site v.sampler (p side))).val:Word w) ∧
      ((tr).oldRole side).read output (i.val:Word w)=(ProtocolRAMTurnOperands.printed v.sampler false p side false:Word w) := by
  intro i p
  have room:=within.trans_lt native
  have numeric : work+7*oldRows+4*rows<2^w:=by change work+4*oldRows+4*rows+3*oldRows<2^w at room; clear * - room; omega
  have sourceRoom : oldRows≤2^w:=by clear * - numeric; omega
  have starts:=v.wide_replayed_start h width ss
  have ready:=v.wide_signed_turn_ready_at h width stock ((lw).bank last) ss work (v.fixedTerminalStock_end P h width)
    (starts.1.trans replayed) (starts.2.trans replayed) numeric
  have high : (z).ceiling hi<2^w:=(starts.1.trans replayed).trans_lt (by clear * - numeric; omega)
  obtain ⟨pre,ranked,low,amount⟩:=RankTape.Observation.read ranker mount o observed rfl
  have floor : rankFirst≤(rpage).rankStart:=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have saved (a) (ha : a<extent₀) := (ranked.frame a (ha.trans_le (within.trans floor))).trans
    ((low a (ha.trans_le within)).trans (frozen a ha))
  have seen:=v.wide_spill_original_goods h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ work initial output initialLow high sourceRoom i (.inl good)
    ((encode).symm_apply_apply _) ready.1 ready.2 room saved sites
  exact fun side=>⟨(seen side).1,(seen side).2.2⟩

theorem wide_spill_turn_original_roles (initial rankedInput output : Memory w)
    (initialLow : ∀x<full,initial x=settled x)
    (frozen : ∀x<extent₀,rankedInput x=(tr).extendedState stk initial x)
    (observed : RankTape.Observation ranker mount o j.val rankedInput output)
    (replayed : v.wideReplayedTurnBase h width ss≤work) (within : extent₀≤rankFirst)
    (oldWindow : v.wideTerminalWorkEnd h width bits work≤turnFirst)
    (_rankWindow : (rpage).offsetsStart≤turnFirst) (headroom : rankFirst≤turnFirst) (word : turnFirst<2^w)
    (sites : siteLast h D k+1≤2^w) (good : Goods h v.W k) :
    let i:=(encode) (.inr (.inl good))
    let p:=publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr (.inl good))
    let vals:=ProtocolRAMTurnSnapshot.values (panel).banks output
    ProtocolRAMTurnChart.rev (chart output) i.val=ProtocolRAMTurnStepOrder.reverse mount
      (siteNumber h D k).injective baseChord (.inr (.inl good)) ∧
      vals.oldSource i.val=ProtocolRAMTurnOperands.printed v.sampler false p false false ∧
      vals.oldTarget i.val=ProtocolRAMTurnOperands.printed v.sampler false p true false := by
  intro i p vals
  have cap : 2*slotRoom ≤ 2^w := by
    obtain ⟨_,_,_,shelf,finish⟩ := (win).bounds
    have fits : (win).stop ≤ 2^w := oldWindow.trans word.le
    have positive : 0<(win).sites := Nat.succ_pos _
    have enough : (win).seats ≤ (win).sites*(win).seats := Nat.le_mul_of_pos_left _ positive
    have seats : slotRoom ≤ (win).seats := Nat.le_add_right ..
    clear * - fits shelf finish enough seats
    omega
  have seen:=v.wide_spill_turn_original_words h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ work rankFirst j initial rankedInput output
    initialLow frozen observed replayed within (headroom.trans_lt word) sites good
  apply DateSpill.original_good_roles v.sampler π tr mount baseChord
    (ProtocolRAMTurnReplayed.key (rpage).rankStart (rows+coreCount o))
    (ProtocolRAMTurnReplayed.rank (rpage).rankStart (rows+coreCount o) rows) output i good
    (activePaid v.sampler counts ports) sites seen
  exact fun side=>DateSpill.printed_fit v.sampler false p side cap


omit horizon age budget small operandAge card marks unique A₀ in
private def SparseReadback (rankedInput output : Memory w) (receipt : (panel).Inputs turnFirst output) : Prop :=
  let keep:=ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
  let sparse:=receipt.columns ∘ keep
  let seats:=(ProtocolRAMTurnShelf.restrictedLive receipt.columns keep).trans receipt.put
  ((∀f a,receipt.word f a=ProtocolRAMTurnShelf.entry sparse seats f a) ∧
    ∀i : ProtocolRAMTurnShelf.Live sparse,(seats i).1.val=
    ((ProtocolRAMDateSpillPosition.sparseSpine v.sampler π mount baseChord
      (((mount).datedLayout (siteNumber h D k).injective baseChord).num
        (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).1)).visit
      (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).2).val) ∧
    ∀i,sparse i 4=((mount).datedLayout (siteNumber h D k).injective baseChord).bits
      (fun good=>RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot good))
      (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i).1

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseBaseline := Whole.Reconciliation sink original supply who dur ord ci cj archive

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseBought := ∀boughtRow : Fin (P).catalogue.boughtRows, Reads (rawRow ((P).catalogue.boughtIndex boughtRow))
    ((P).catalogue.bought.view chk (boughtRow.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex boughtRow).val)

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseSettled := settled

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseCounts := counts

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseMount := mount

omit horizon age budget small operandAge card marks unique A₀ in
private abbrev sparseCheckout := chk

variable (initial rankedInput output romInput : Memory (Native.wordBits h (2^v.W) Native.copies))
    (baseline : sparseBaseline v h width size M π raw bits issues who cj)
    (bought : sparseBought v h width size M π raw bits issues who cj)
    (cost : ∀e : Fin (v.widePlacement h width).catalogue.rows,
      PaidWidths.total (v.widePaidSlices h width bits) (sparseCheckout v h width size M π raw bits) e +(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^(Native.wordBits h (2^v.W) Native.copies))
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (invoiceInput : ∀a<(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh,rankedInput a=sparseCheckout v h width size M π raw bits a)
    (initialLow : ∀a<v.wideFundedSize h width bits,initial a=sparseSettled v h width size M π raw bits issues who cj a) (rankLow : ∀a<v.wideFundedSize h width bits,rankedInput a=sparseSettled v h width size M π raw bits issues who cj a)
    (extended : ∀a<((v.wideTerminalBoard h width bits work).endAt + 3*Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows)),rankedInput a=(v.wideTerminalBoard h width bits work).extendedState (v.wideTerminalStock h width bits) initial a)
    (observed : RankTape.Observation (v.wideSpillRanks h width bits rankFirst)
      (sparseMount v h width size M π raw bits) (wideRouteOrder h (2^v.W) k) j.val rankedInput output)
    (oldQty : Fin (Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows))→ℕ) (oldPort : ∀i,0<oldQty i→Bool→Public v.sampler h v.W k v.wideJobs)
    (capturedPorts : (v.wideTerminalBoard h width bits work).LiveReads v.sampler oldQty
      (sparseCounts v h width size M π raw bits issues who cj) oldPort
      (fun e on side=>Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side))) output)
    (retainedROM : ∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM work→
      output a=v.wideTerminalWords h width bits terminalROM work romInput a)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM work≤work)
    (replayed : v.wideReplayedTurnBase h width (v.widePaidSlices h width bits)≤work) (within : ((v.wideTerminalBoard h width bits work).endAt + 3*Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows))≤rankFirst)
    (oldWindow : v.wideTerminalWorkEnd h width bits work≤turnFirst)
    (rankWindow : (v.wideSpillPage h width bits rankFirst j.val).offsetsStart≤turnFirst) (headroom : rankFirst≤turnFirst) (word : turnFirst<2^(Native.wordBits h (2^v.W) Native.copies))
    (left : (v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
      oldStart newStart leftOnly rightOnly j).left.prefix.Fits (Native.wordBits h (2^v.W) Native.copies) turnFirst) (right : (v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
      oldStart newStart leftOnly rightOnly j).right.prefix.Fits (Native.wordBits h (2^v.W) Native.copies) turnFirst)
include baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed capturedPorts
  retainedROM readOnly replayed within oldWindow rankWindow headroom word left right


/-- The original calendar and funded terminal archives determine every active source
and both of every visited paid edge's endpoint words. -/
private def fundedSpillChart :
    {receipt : (panel).Inputs turnFirst output // SparseReadback (v:=v) (h:=h) (width:=width) (bits:=bits) (π:=π) (M:=M) (raw:=raw) (size:=size)
       (datedROM:=datedROM) (terminalROM:=terminalROM) (work:=work) (rankFirst:=rankFirst)
       (turnFirst:=turnFirst) (oldStart:=oldStart) (newStart:=newStart) (leftOnly:=leftOnly) (rightOnly:=rightOnly)
       (j:=j) rankedInput output receipt} := by
  let workRoom : (win).stop≤2^w:=oldWindow.trans word.le
  have sites : (T).sites≤2^w := by
    obtain ⟨hzero,hsrc,hbase,hscratch,hstop⟩:=(win).bounds
    have seats : 0<(win).seats:=by change 0< slotRoom+(1+9*k);omega
    have fit:=(Nat.le_mul_of_pos_right (win).sites seats)
    change (win).sites≤2^w
    omega
  have lengths (i : Fin oldRows) : ProtocolRAMTurnGeometry.length (decode i)<2^w := by
    obtain ⟨hzero,hsrc,hbase,hscratch,hstop⟩:=(win).bounds
    let lens:=ProtocolRAMTurnGeometry.length ∘ decode
    have count : (T).turns=∑i,ProtocolRAMTurnOrder.width lens i:=rfl
    have row : ProtocolRAMTurnOrder.width lens i≤∑j,ProtocolRAMTurnOrder.width lens j:=
      Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    have length : (win).rows=(T).turns:=rfl
    change lens i<2^w
    have span : lens i+1≤(win).rows := row
    omega
  have live:=v.wide_spill_turn_active h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput output initialLow rankLow extended observed replayed within (headroom.trans_lt word) sites baseChord
  let existsRank:=RankTape.Observation.read ranker mount o observed rfl
  let origin:=Classical.choose existsRank
  have rank:= (Classical.choose_spec existsRank).1
  let spill:=fun x : Goods h v.W k=>RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot x)
  have loadPaid (e : Fin rows) : routeLoad (mount).ordinary spill e≤counts e:=
    v.wide_spill_turn_invoice h width size M π raw bits horizon age budget small issues who cj
      rankFirst j rankedInput baseline cost rad paidAge invoiceInput e
  have position (e : {e : Fin rows // 0<counts e}) :
      filledChord (mount).actual baseChord e.val=HistoryRoles.sorted v.sampler π v.depth marks (.inl (A₀.ident e)) :=
    CatalogueRows.Alignment.mounted_chord v.sampler π v.depth marks (P).catalogue order
      (v.wideBoughtOrdinal h width π marks) rawRow A₀ baseChord chk bought e
  have active (i : Fin oldRows) (yes : 0<(chart output).width ((encode) ((decode) i)).val) :
      ∃g,(decode) i=.inr (.inl g) ∧ (panel).data.rawSource.read output (((encode) ((decode) i)).val:Word w)=
        (ProtocolRAMTurnEdges.visit mount (siteNumber h D k).injective baseChord ((decode) i) 0:Word w) ∧
        (chart output).sourceRole ((encode) ((decode) i)).val<2*slotRoom ∧
        (chart output).targetRole ((encode) ((decode) i)).val<2*slotRoom := by
    obtain ⟨g,ty,first,source,target,_⟩:=live i yes
    exact ⟨g,ty,first,source,target⟩
  have halves:=DateSpill.paid_halves v.sampler π tr mount baseChord o v.depth marks unique decode
    (fun i=>(chart output).width ((encode) ((decode) i)).val) spill oldQty counts oldPort _
    A₀.ident position (fun _ _ _=>rfl) output capturedPorts (fun i yes=>by
      obtain ⟨g,ty,_,_,_,mass⟩:=live i yes
      exact ⟨g,ty,lt_of_lt_of_eq yes mass⟩) loadPaid
  let receipt:=v.wide_spill_turn_chart h width bits datedROM terminalROM work rankFirst turnFirst
    oldStart newStart leftOnly rightOnly j mount baseChord marks unique romInput output origin rank retainedROM
    readOnly oldWindow rankWindow word left right sites lengths active halves
  have count (g : Goods h v.W k) : (chart output).width ((encode) (.inr (.inl g))).val=spill g :=
    v.wide_spill_turn_goods_width h width size M π raw bits horizon age budget small issues card who cj
      datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j rankedInput output
      rankLow observed (by have size₀:=within.trans headroom;change work+4*oldRows+4*rows+3*oldRows≤turnFirst at size₀;omega) g
  have ordinary (x : RawOld) (on : 0<(chart output).width ((encode) x).val) : ∃g,x=.inr (.inl g) := by
    have positive : 0<(chart output).width ((encode) ((decode) ((encode) x))).val :=
      by simpa only [Equiv.symm_apply_apply] using on
    obtain ⟨g,eqn,_⟩:=active ((encode) x) positive
    exact ⟨g,by simpa only [Equiv.symm_apply_apply] using eqn⟩
  refine ⟨receipt,v.wide_spill_turn_chart_word h width bits datedROM terminalROM work rankFirst turnFirst
    oldStart newStart leftOnly rightOnly j mount baseChord marks unique romInput output origin rank retainedROM
    readOnly oldWindow rankWindow word left right sites lengths active halves,?_⟩
  exact fun i=>ProtocolRAMDateSpillPosition.chart_widths v.sampler π mount baseChord o slotRoom (chart output)
    (ProtocolRAMTurnSnapshot.values (panel).banks output) receipt.oldBase receipt.newBase spill count ordinary i

local notation "funded" => fundedSpillChart v h width size M π raw bits horizon age budget small operandAge
  issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
  initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
  oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right

/-- Native executable inputs for the originally charged date. -/
def wide_spill_turn_funded_chart : (panel).Inputs turnFirst output := (funded).1

/-- The five physical window words are the row-restriction to the real sparse positions,
and every surviving position is installed at the true original site. -/
theorem wide_spill_turn_funded_chart_word :
    let receipt:=(funded).1
    let keep:=ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
    let sparse:=receipt.columns ∘ keep
    let seats:=(ProtocolRAMTurnShelf.restrictedLive receipt.columns keep).trans receipt.put
    (∀f a,receipt.word f a=ProtocolRAMTurnShelf.entry sparse seats f a) ∧
      ∀i : ProtocolRAMTurnShelf.Live sparse,(seats i).1.val=
      ((ProtocolRAMDateSpillPosition.sparseSpine v.sampler π mount baseChord
        (((mount).datedLayout (siteNumber h D k).injective baseChord).num
          (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).1)).visit
        (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i.val).2).val := (funded).2.1

/-- Evaluation of every native descriptor on the retained RAM. -/
theorem wide_spill_turn_funded_columns (i : Fin (T).turns) :
    let receipt:=(funded).1
    let len:=ProtocolRAMTurnGeometry.length (h:=h) (d:=D) (k:=k) (edges:=rows) ∘ decode
    let vis:=ProtocolRAMVisitAdjacency.vertex len
      (fun a=>ProtocolRAMTurnEdges.visit mount (siteNumber h D k).injective baseChord ((decode) a))
    let u:=ProtocolRAMTurnGeometry.header o slotRoom decode
    receipt.columns i=DateSpill.Turns.fieldWords (ProtocolRAMTurnChart.record u (chart output) vis i)
      (ProtocolRAMTurnSnapshot.values (panel).banks output) (fun n=>((panel).left.prefix.eval output (n:Word w)).val)
      (fun n=>((panel).right.prefix.eval output (n:Word w)).val) := rfl

theorem wide_spill_turn_funded_widths :
    let receipt:=(funded).1
    let keep:=ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
    ∀i,receipt.columns (keep i) 4=((mount).datedLayout (siteNumber h D k).injective baseChord).bits
      (fun good=>RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot good))
      (ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord i).1 := (funded).2.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
