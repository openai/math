import OAI.Hierarchy.TaggedWireFundedReport
import OAI.Hierarchy.ProtocolRAMTurnSettlementWeights
import OAI.Hierarchy.ProtocolRAMTurnSettlementBanks
import OAI.Hierarchy.TaggedWireMountedChord
import OAI.Hierarchy.ProtocolRAMTurnReportEvidence
import OAI.Hierarchy.ProbeFixedWideTerminalRun

namespace OAI
/-! # Executing the paid physical terminal for the original funded report -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
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
local notation "cj" => pairKeys (Columns h D) k
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who
      (CatalystArchive.pairKeys (Columns h (2^v.W)) k) marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)


local notation "paidAtLast" => (lw).bank last
variable (rom work : ℕ)
local notation "T" => v.wideTerminal h width bits rom work
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "lo" => v.wideTerminalRankStart h width bits work
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
local notation "oIdx" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "pad" => publicChord h D k
local notation "port" => Public v.sampler h v.W k v.wideJobs

private theorem funded_rank_room {workStart oldCount edgeCount slotCount oldSpan edgeSpan rankSize lastSize rankStart floorAddr wordLimit : ℕ}
    (rank_eq : rankStart=workStart+4*oldCount+4*edgeCount+3*oldCount+oldSpan+edgeSpan)
    (floor_eq : floorAddr=rankStart+rankSize+rankSize+2*(edgeCount+slotCount)+3*(edgeCount+slotCount)+4*(edgeCount+slotCount)+edgeCount+3+lastSize)
    (high : floorAddr<wordLimit) : workStart+7*oldCount+4*edgeCount<wordLimit ∧ workStart≤rankStart ∧ rankStart<wordLimit := by
  omega

private theorem funded_bank_room : (stock).base+(stock).size≤2^page ∧ rows≤2^page := by
  have stockFits : (stock).base+(stock).size≤2^page := by
    have bound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
    have inside:=v.fixedTerminalStock_end P h width
    unfold TerminalLayout.footprint at bound
    omega
  have rowsFit : rows≤2^page := by
    have bound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at bound
    omega
  exact ⟨stockFits,rowsFit⟩

attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages Sink.output Sink.terminalRows
  wideFundedSize wideSignedCheckoutAt wideSignedMidAt

/-- The printed rank tape and the original input of the funded matrix use the same weight
at every ledger occurrence, including multiple occurrences of one edge. -/
theorem wide_funded_terminal_widths
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    let B:=(mount).matrixLayout (siteNumber h D k).injective pad
    B.nativeWidth ord paid (fun i=>RouteSettlement.actual (old).stock settled (ci i))
      (fun j=>RouteSettlement.actual (old).reserved settled (cj j).val)
      (fun j=>RouteSettlement.actual (old).used settled (cj j).val)=
      B.nativeWidth ord Z.fixed Z.stock Z.reserved Z.used := by
  intro Z B
  obtain ⟨stockFits,rowsFit⟩:=funded_bank_room v h width
  exact TerminalLayout.turn_width page (P).catalogue stock _ B ord ci (fun j=>(cj j).val)
    closed paid stockFits rowsFit

private def fundedPositiveCast {n : ℕ} (left right : Fin n → ℕ)
    (agree : ∀i, left i=right i) : {i // 0<left i} ↪ {i // 0<right i} :=
  ⟨fun i=>⟨i.val,i.property.trans_eq (agree i.val)⟩,fun _ _ eq=>
    Subtype.ext (congrArg (fun e : {e : Fin n // 0<right e}=>e.val) eq)⟩

include operandAge card in
/-- The actual post-date cut supplies its preserved words, both public bounds, and the last
pre-settlement paid page. All labels and slot selectors are obtained from the same funded
report and the original native circuit. -/
theorem wide_funded_terminal_at (initial m : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (charged : ∀j : Fin num,RouteSettlement.actual (old).used closed j.val=
      usedAt (CatalystArchive.site v.mesh issues) dur j ∧ RouteSettlement.actual (old).reserved closed j.val=supply)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (keep : ∀x,x<full→m x=settled x)
    (lastRead : ∀i : Fin rows,(m ((paidAtLast).base+i.val)).val=paid i)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (afterReplay : v.wideReplayedTurnBase h width ss≤work)
    (room : v.wideTerminalWorkEnd h width bits work≤2^w)
    («public» : ∀x,rom≤x→x<v.wideTerminalROMEnd h width bits rom work→
      m x=v.wideTerminalWords h width bits rom work initial x)
    (romBefore : v.wideTerminalROMEnd h width bits rom work≤work) (archiveRows : Bool := false) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    let available:=SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
    let before := fun (i : Fin (tr).old) (_ : 0<available i) (side : Bool) =>
      publicRoleFor v.sampler π (Z.beforePay v.depth marks unique A₀.ident) (SettledMatrix.Layout.numbered i) side
    let after := fun (i : Fin rows) (on : 0<(Z.rows i).width) (side : Bool) =>
      (Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨i,on⟩,side)) : port)
    let fixed:=fun i : Fin rows => available (oIdx (.inl i))
    let into:=fundedPositiveCast fixed Z.fixed (fun i=>
      congrArg (SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used)
        ((oIdx).symm_apply_apply (.inl i)))
    let ident:=into.trans (Z.fixedOriginal v.depth marks A₀.ident)
    let B:=(mount).matrixLayout (place).injective pad
    let native:=B.nativeEdge ord
    let loads:=B.nativeWidth ord paid (fun i=>RouteSettlement.actual (old).stock settled (ci i))
      (fun j=>RouteSettlement.actual (old).reserved settled (cj j).val)
      (fun j=>RouteSettlement.actual (old).used settled (cj j).val)
    let header:=ProtocolRAMTurnGeometry.header o (WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler) names
    let visit:=ProtocolRAMVisitAdjacency.vertex (ProtocolRAMTurnGeometry.length ∘ names)
      (fun a=>ProtocolRAMTurnEdges.visit mount (place).injective pad (names a))
    ∃post : Memory w,
      let cols:=ProtocolRAMTurnInstalled.columns
        (ProtocolRAMTurnChart.record header (ProtocolRAMTurnChart.captured (T).columns post) visit)
        (ProtocolRAMTurnSnapshot.values (T).walk post)
      ∃(kept : ∀j : ProtocolRAMTurnShelf.Live cols, ProtocolRAMLiveTurnOrder.retain fixed
          (ProtocolRAMPaidTurnPlacement.rawItem names j.val).1) (out : Memory w),
      ((T).code w paidAtLast).Exec m out ((T).ticks paidAtLast) ∧
      (∀f : Fin 5, ∀seat : ProtocolRAMTurnShelf.Seats (T).sites (T).seats,
        out ((T).base+f.val*((T).sites*(T).seats)+seat.1.val*(T).seats+seat.2.val)=
          ProtocolRAMTurnShelf.entry cols
            (ProtocolRAMPaidTurnPlacement.chartPut v.sampler π v.depth marks unique mount pad fixed ident names cols kept) f seat) ∧
      (∀x<work,out x=m x) ∧ (∀x<(v.wideTurnWindow h width bits work).floor,out x=post x) ∧
      (tr).LiveReads v.sampler available (fun i=>(Z.rows i).width) before after post ∧
      (∀i : Fin (rows+r),post (ProtocolRAMTurnReplayed.ranks lo (rows+r) rows+4*i.val+3)=
        (TaggedShorterCommonScan.earlier native loads i.val (native i):Word w)) ∧
      (∀i : Fin (rows+r),post (lo+i.val)=((native i).val:Word w)) ∧
      let masses:=∀i : Fin (rows+r),post ((ProtocolRAMTurnReplayed.weight lo (rows+r)).base+i.val)=(loads i:Word w)
      if archiveRows then (∀a<lo,post a=(tr).extendedState (T).stock m a) ∧ masses else masses :=
  let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
  let win:=v.wideTurnWindow h width bits work
  have high : win.floor<2^w := by
    obtain ⟨hzero,hsrc,hbase,hscratch,hstop⟩:=win.bounds
    have ready : win.stop≤2^w:=room
    omega
  have ab : 28*2^page≤(lw).archive:=v.wide_prefix_starts h width ss
  have frontier := v.wide_replayed_start h width ss
  have roleFloor : (lw).archive≤work := frontier.1.trans afterReplay
  have lastFits : (paidAtLast).base+(paidAtLast).size≤work := frontier.2.trans afterReplay
  have archiveBound : (lw).archive = full := by unfold wideFundedSize; rfl
  have archiveKeep (x : ℕ) (hx : x<(lw).archive) : m x=settled x := keep x (hx.trans_le archiveBound.le)
  have rowSize : rows≤(paidAtLast).size := (lw).covered
  have lastBase : (paidAtLast).base+rows≤work := (Nat.add_le_add_left rowSize _).trans lastFits
  have rankStartBound : lo=work+4*(tr).old+4*rows+3*(tr).old+ProtocolRAMPurchaseSampler.span (tr).old+
      ProtocolRAMPurchaseSampler.span rows := rfl
  have floor : win.floor=lo+2^ProtocolRAMPackedRanked.groupBits (rows+r)+2^ProtocolRAMPackedRanked.groupBits (rows+r)+
      2*(rows+r)+3*(rows+r)+4*(rows+r)+rows+3+2^ProtocolRAMPackedRanked.groupBits (4*(rows+r)) := rfl
  have ⟨operandRoom,workRank,rankWord⟩ := funded_rank_room rankStartBound floor high
  have paidSmall : rows<2^w := by omega
  have ⟨stockFits,rowsFit⟩:=funded_bank_room v h width
  have capacity (c : Bank) (hc : c∈[(old).index,(old).kind,(old).stock,(old).reserved,(old).used]) :
      c.base+c.size≤(lw).archive := (TerminalLayout.turn_location page stock c hc stockFits).1.trans (by omega)
  have frames (c : Bank) (hc : c∈[(old).index,(old).kind,(old).stock,(old).reserved,(old).used]) (j : Word w) :
      c.read settled j=c.read closed j :=
    TerminalLayout.turn_read page (P).catalogue stock _ ord ci _ closed c hc stockFits rowsFit j
  have working (c : Bank) (hc : c∈[(old).index,(old).kind,(old).stock,(old).reserved,(old).used]) (j : Word w) :
      c.read m j=c.read closed j := by
    have low:=capacity c hc
    exact (archiveKeep (c.base+j.val%c.size) ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos c.bits)) _).trans_le low)).trans
      (frames c hc j)
  let mounted:=baseline.ports.mounted original supply who dur baseline.archive baseline.usedSize baseline.reserveSize
    baseline.funded baseline.word
  have directoryRead:=TerminalLayout.turn_directory page (P).catalogue stock _ ord ci (fun j=>(cj j).val)
    closed mounted.directory stockFits rowsFit
  have inputs (c : Bank) (hc : c∈[paidAtLast,(old).index,(old).kind,(old).stock,(old).reserved,(old).used]) : c.Fits w lo := by
    rcases List.mem_cons.mp hc with hpaid|hold
    · subst c
      exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
    · have bound:=capacity c hold
      exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have limited (j : Columns h D×Fin k) : RouteSettlement.actual (old).used settled (cj j).val≤
      RouteSettlement.actual (old).reserved settled (cj j).val := by
    have one:=congrArg Fin.val (frames (old).used (by simp) ((cj j).val:Word w))
    have two:=congrArg Fin.val (frames (old).reserved (by simp) ((cj j).val:Word w))
    exact (show RouteSettlement.actual (old).used settled (cj j).val=RouteSettlement.actual (old).used closed (cj j).val from one).le.trans
      ((mounted.available j).trans (show RouteSettlement.actual (old).reserved closed (cj j).val≤RouteSettlement.actual (old).reserved settled (cj j).val from two.symm.le))
  have money (i : Fin rows) : ((paidAtLast).read m (i.val:Word w)).val=Z.fixed i := by
    change (m ((paidAtLast).base+(i.val:Word w).val%(paidAtLast).size)).val=paid i
    rw [Fin.val_cast_of_lt (i.isLt.trans paidSmall),Nat.mod_eq_of_lt (i.isLt.trans_le rowSize)]
    exact lastRead i
  have goodsLive (i : Goods h v.W k) : ((stock).read m ((ci i):Word w)).val=Z.stock i :=
    congrArg Fin.val (working (old).stock (by simp) _)
  have heldLive (i : Catalysts h v.W k) : supply=Z.reserved i := (charged (cj i)).2.symm
  have usedLive (i : Catalysts h v.W k) : RoleRoom.usedBy v.mesh issues i=Z.used i := (charged (cj i)).1.symm
  let available:=SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
  let markedID:=A₀.ident
  let beforeAt (i : Fin (tr).old) side : port :=
    publicRoleFor v.sampler π (Z.beforePay v.depth marks unique markedID) (SettledMatrix.Layout.numbered i) side
  let before (i : Fin (tr).old) (_ : 0<available i) := beforeAt i
  let after (i : Fin rows) (on : 0<(Z.rows i).width) side : port :=
    .inl (HistoryRoles.paid v.sampler π v.depth marks unique (markedID ⟨i,on⟩,side))
  let run:=v.wide_funded_turn_live h width size M π raw bits horizon age budget small operandAge issues card
    who cj marks unique A₀ work m baseline charged keep lastRead cost afterReplay operandRoom
  have live : (tr).LiveReads v.sampler available (fun i=>(Z.rows i).width) before after ((tr).extendedState (T).stock m) := by
    let seen := SettledMatrix.Layout.bits (fun e : Fin rows=>((paidAtLast).read m (e.val:Word w)).val)
      (fun i : Goods h v.W k=>((stock).read m ((ci i):Word w)).val)
      (fun _ : Catalysts h v.W k=>supply) (RoleRoom.usedBy v.mesh issues)
    have amounts_eq : seen=available :=
      congr (congr (congr (congrArg SettledMatrix.Layout.bits (funext money))
        (funext goodsLive)) (funext heldLive)) (funext usedLive)
    let observed (f : Fin (tr).old→ℕ) := (tr).LiveReads v.sampler f (fun i=>(Z.rows i).width)
      (fun i _=>beforeAt i) after ((tr).extendedState (T).stock m)
    have recorded : observed seen := run.2
    exact Eq.mp (congrArg observed amounts_eq) recorded
  have aligned (i : {i : Fin rows // 0<(Z.rows i).width}) :
      filledChord (mount).actual pad i.val=HistoryRoles.sorted v.sampler π v.depth marks (.inl (markedID i)) :=
    CatalogueRows.Alignment.mounted_chord v.sampler π v.depth marks (P).catalogue order
      (v.wideBoughtOrdinal h width π marks) rawRow A₀ pad chk read i
  have large : (T).sites≤2^w := by
    have positive : 0<win.seats := by
      change 0<WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler+(1+9*k)
      omega
    have product : win.sites≤win.sites*win.seats := Nat.le_mul_of_pos_right _ positive
    obtain ⟨hzero,hsrc,hbase,hscratch,hstop⟩:=win.bounds
    have ready : win.stop≤2^w:=room
    change win.sites≤2^w
    omega
  have lengths (i : Fin (tr).old) : ProtocolRAMTurnGeometry.length (names i)<2^w := by
    let lens:=ProtocolRAMTurnGeometry.length ∘ names
    have count : (T).turns=∑i,ProtocolRAMTurnOrder.width lens i:=rfl
    have here : ProtocolRAMTurnOrder.width lens i≤∑j,ProtocolRAMTurnOrder.width lens j:=
      Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    obtain ⟨hzero,hsrc,hbase,hscratch,hstop⟩:=win.bounds
    have span : win.rows=(T).turns:=rfl
    have stop : win.stop≤2^w:=room
    have routeBound : lens i < (T).turns :=
      (Nat.lt_succ_self _).trans_le (here.trans_eq count.symm)
    have seatsBound : win.rows ≤ 2^w := by omega
    exact routeBound.trans_le (span.symm.le.trans seatsBound)
  have numberAt (src : ProtocolRAMTurnGeometry.Source rows h D k) :
      SettledMatrix.Layout.numbered (oIdx src)=src := (oIdx).symm_apply_apply src
  have massAt (src : ProtocolRAMTurnGeometry.Source rows h D k) :
      available (oIdx src)=SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used src :=
    congrArg (SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used) (numberAt src)
  have oldAt (i : Fin rows) : available (oIdx (.inl i))=Z.fixed i := massAt (.inl i)
  let into : {i : Fin rows // 0<available (oIdx (.inl i))} ↪ {i : Fin rows // 0<Z.fixed i} :=
    fundedPositiveCast (fun i : Fin rows => available (oIdx (.inl i))) Z.fixed oldAt
  let ident:=into.trans (Z.fixedOriginal v.depth marks markedID)
  v.wide_terminal_run h width bits rom work mount pad marks unique initial settled m (paidSource:=chk)
    ci (fun j=>(cj j).val) directoryRead capacity archiveKeep lastRead lastBase
    inputs limited ⟨run.1,live⟩ «public» romBefore room large lengths
    (fun a on=>by
      change (HistoryRoles.name (HistoryRoles.site v.sampler (publicRoleFor v.sampler π
        (Z.beforePay v.depth marks unique markedID) (SettledMatrix.Layout.numbered (oIdx (names a))) false))).val=_
      exact (congrArg (fun src=>(HistoryRoles.name (HistoryRoles.site v.sampler
        (publicRoleFor v.sampler π (Z.beforePay v.depth marks unique markedID) src false))).val)
        (numberAt (names a))).trans
        (Z.start_from_report v.depth marks unique markedID aligned (names a) (on.trans_eq (massAt (names a)))))
    (fun a on j hj=>Z.ends_from_report v.depth marks unique markedID aligned o (names a)
      (on.trans_eq (massAt (names a))) j hj)
    ident
    (fun i=>Z.fixedOriginal_position v.depth marks markedID aligned (into i))
    (fun i=>by
      obtain ⟨flip,ports⟩:=Z.fixed_from_report v.depth marks unique markedID (into i)
      refine ⟨flip,fun side=>?_⟩
      change publicRoleFor v.sampler π (Z.beforePay v.depth marks unique markedID)
        (SettledMatrix.Layout.numbered (oIdx (.inl i.val))) side=_
      exact (congrArg (fun src=>publicRoleFor v.sampler π (Z.beforePay v.depth marks unique markedID)
        src side) (numberAt (.inl i.val))).trans (ports side)) archiveRows

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
