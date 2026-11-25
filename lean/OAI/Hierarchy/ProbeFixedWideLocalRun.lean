import OAI.Hierarchy.ProbeFixedWideOriginalDates
import OAI.Hierarchy.ProbeFixedFundedShelfContents
import OAI.Hierarchy.TaggedWideTerminalROM

namespace OAI
/-! # Running original dates followed by the paid five-field terminal in the installed CPU -/

set_option quotPrecheck false

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped BigOperators Classical Fin.CommRing
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
variable (horizon : v.wideFundedSize h width (v.maxBits) ≤ size) (age : v.wideFundedHeight≤h)
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
    (A₀ : WideFundedTurnAlignment v h width size M π raw (v.maxBits) issues who
      (CatalystArchive.pairKeys (Columns h (2^v.W)) k) marks)

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
local notation "dst" => TerminalLayout.destination page
local notation "tb" => v.wideTerminalBoard h width bits 0

/-- Public chronological candidate ordinal in the real rectangular archive. -/
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


open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "actual" => fun i : Fin rows=>decide ((P).catalogue.transport order i)
local notation "markedID" => A₀.ident
local notation "locked" => (lw).bank last
local notation "amount" => SettledMatrix.Layout.bits paid goods held taken
local notation "outputRole" => CatalogueRows.Alignment.originalPort v.sampler π v.depth marks unique (P).catalogue order
    (v.wideBoughtOrdinal h width π marks) rawRow A₀

variable (ell unitCost rom work : ℕ)
local notation "dated" => v.wideDated h width ell unitCost
local notation "tRom" => (dated).romEnd rom
local notation "tWork" => (dated).workEnd work
local notation "T" => v.wideTerminal h width bits tRom tWork
local notation "board" => v.wideTerminalBoard h width bits tWork
local notation "dates" => ProcedureBank.program (WideCPU.Dated.last last)
    (fun i=>((dated).sheets rom work i).code w)

private theorem local_window_room (windowLayout : ProtocolRAMTurnWindow.Layout) :
    windowLayout.floor < windowLayout.stop := by
  obtain ⟨zeroRoom,sourceRoom,baseRoom,scratchRoom,stopRoom⟩ := windowLayout.bounds
  omega

include operandAge card
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages Sink.output Sink.terminalRows
  wideFundedSize wideSignedCheckoutAt wideSignedMidAt

/-- All three batches of dated controls, the frozen width and both immutable physical slots
remain available beside the native five terminal fields. The nine original emitted words
also survive the full local CPU program. -/
theorem wide_local_run (m seedTerms : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (charged : ∀j : Fin num,RouteSettlement.actual (old).used closed j.val=
      usedAt (CatalystArchive.site v.mesh issues) dur j ∧ RouteSettlement.actual (old).reserved closed j.val=supply)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (keep : ∀a,a<full→m a=settled a)
    (lastPaid : ∀i:Fin rows,(m ((locked).base+i.val)).val=paid i)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (activeAge : v.wideDatedSupportHeight≤h)
    (ballotAge : v.wideBallotHeight≤h) (nativeRadius : M=v.radius)
    (afterReplay : v.wideReplayedTurnBase h width ss≤work)
    (top : (A).endAddress v.mesh≤rom) (funded : full≤work)
    (gap : 3*tRom+2≤work)
    (publicRoom : v.wideTerminalROMEnd h width bits tRom tWork≤work)
    (room : v.wideTerminalWorkEnd h width bits tWork≤2^w)
    (headerSeed emittedInput : Memory w)
    (rawFrame : ∀a,dst≤a→a<dst+9*rows→m a=ProtocolRAMEmit.emitted dst rawRow emittedInput a)
    (beforeROM : dst+6*rows+ProtocolRAMPurchaseSampler.span (3*rows)≤rom)
    (sources : ∀a,a<(A).endAddress v.mesh→m a=chk a)
    (dateROM : ∀a,rom≤a→a<tRom→m a=
      (dated).words rom (SiteDirectory.table h D k) actual headerSeed a)
    (terminalROM : ∀a,tRom≤a→a<v.wideTerminalROMEnd h width bits tRom tWork→
      m a=v.wideTerminalWords h width bits tRom tWork seedTerms a) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    let oldPort:=HistoryRoles.Terminal.ports v.sampler π v.depth marks unique Z.fixed Z.stock Z.reserved Z.used
      (Z.fixedOriginal v.depth marks markedID)
    let oldCode:=fun i side=>if on:0<SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used i then labelled v.sampler false (oldPort ⟨(i,side),on⟩) else 0
    let newCode:=fun i side=>if on:0<(rawRow i).width then labelled v.sampler true (outputRole ⟨i,on⟩ side) else 0
    ∃(after out : Memory w),
      ((dates).seq ((T).code w locked)).Exec m out ((∑i,((dated).sheets rom work i).ticks)+(T).ticks locked) ∧
      (∀a,a<work → out a=m a) ∧
      (∀a,dst≤a→a<dst+9*rows → out a=ProtocolRAMEmit.emitted dst rawRow emittedInput a) ∧
      (∀j:Fin (last+1),∀f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
        ((dated).roleStart work j) (value j.val ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) out f) ∧
      (∀i : Fin rows,((dated).stageWidth work).read out ((3*i.val:ℕ):Word w)=
        ((if actual i then (rawRow i).width else 0:ℕ):Word w)) ∧
      (∀b,∀i : Fin rows,((dated).slotBank work b).read out (i.val:Word w)=
        ((dated).lanes:Word w)*((dated).orderedSlot b).eval m (i.val:Word w)) ∧
      Z.ShelfContents (T).seats (T).turns (T).base out oldCode newCode ∧
      (dates).Exec m after (∑i,((dated).sheets rom work i).ticks) ∧
      ((T).code w locked).Exec after out ((T).ticks locked) ∧
      (∀a,a<work→after a=m a) ∧ (∀a,a<tWork → out a=after a) ∧
      (∀a,a<(board).endAt+3*(board).old → out a=(board).extendedState (T).stock after a) ∧
      (board).LiveReads v.sampler amount counts
        (fun i _ side=>publicRoleFor v.sampler π (Z.beforePay v.depth marks unique A₀.ident)
          (SettledMatrix.Layout.numbered i) side)
        (fun e on side=>.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side))) out := by
  intro Z oldPort oldCode newCode
  have datedTop : work≤tWork := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart WideCPU.Dated.maskStart WideCPU.Dated.controlStart
      WideCPU.Dated.rolesEnd WideCPU.endOf
    omega
  have first : tWork<v.wideTerminalWorkEnd h width bits tWork := by
    obtain ⟨boardStart,roleEnd,windowStart,_,_,_⟩ :=
      v.wide_terminal_role_floors h width bits tWork room
    have workToFloor : tWork≤(v.wideTurnWindow h width bits tWork).floor :=
      boardStart.trans ((Nat.le_add_right _ _).trans (roleEnd.trans windowStart))
    exact workToFloor.trans_lt (local_window_room _)
  have oldEnd : (v.wideReserveLayout h width ss).scratch≤work :=
    (Nat.le_add_right _ _).trans afterReplay
  obtain ⟨after,didDates,roleReads,widthReads,portReads,low⟩:=
    v.wide_original_dates h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
      m pages baseline keep cost highFit activeAge ballotAge nativeRadius ell unitCost rom work oldEnd top funded
      gap (first.trans_le room) headerSeed emittedInput rawRow actual rawFrame beforeROM sources dateROM
  have paidEnd:= (v.wide_replayed_start h width ss).2
  have paidSize:= (lw).covered
  have afterPaid (i : Fin rows) : (after ((locked).base+i.val)).val=paid i := by
    have bound : (locked).base+i.val<work := by
      have roomPaid : (locked).base+(locked).size≤work:=paidEnd.trans afterReplay
      have capacity : rows≤(locked).size:=paidSize
      omega
    rw [low _ bound,lastPaid]
  have lower (a : ℕ) (ha : a<full) := (low a (ha.trans_le funded)).trans (keep a ha)
  have mounted (a : ℕ) (starts : tRom≤a) (ends : a<v.wideTerminalROMEnd h width bits tRom tWork) :=
    (low a (ends.trans_le publicRoom)).trans (terminalROM a starts ends)
  obtain ⟨out,didTerminal,terminalFrame,extendedWords,finalLive,shelf⟩:=v.wide_funded_shelf_archive h width size M π raw bits horizon age budget small
    operandAge issues card who marks unique A₀ tRom tWork seedTerms after baseline charged read lower afterPaid cost
    (afterReplay.trans datedTop) room mounted (publicRoom.trans datedTop)
  let roleResultAt:=(dated).roleResult (native:=w) rom work v.sampler π v.depth marks unique names
    (fun j:Fin (last+1)=>value j.val ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) (by rfl)
  obtain ⟨roles,widths,slots⟩:=(dated).revenue_frame rom work roleResultAt actual (fun i=>(rawRow i).width)
    m after out terminalFrame roleReads widthReads portReads
  have lowOut (a : ℕ) (ha : a<work) := (terminalFrame a (ha.trans_le datedTop)).trans (low a ha)
  refine ⟨after,out,Procedure.Exec.then didDates didTerminal,lowOut,?_,roles,widths,slots,shelf,didDates,didTerminal,low,terminalFrame,extendedWords,finalLive⟩
  intro a rowLow rowHigh
  have cap:=ProtocolRAMPurchaseSampler.lt_span (3*rows)
  have romRoom : rom≤tRom := by
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.Dated.firstROM,WideCPU.Dated.siteROM,WideCPU.endOf]
    omega
  exact (lowOut a (by omega)).trans (rawFrame a rowLow rowHigh)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Tagged
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {κ A : ℝ} (x : WideParent κ A)
  (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "real" => v.wideDated x.h x.w ell unitCost
local notation "rom" => v.wideInstalledRoot x
local notation "work" => v.wideInstalledSize x m ell unitCost real
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost real
local notation "terminal" => v.wideTerminal x.h x.w v.maxBits ((real).romEnd rom) ((real).workEnd work)
local notation "last" => (events v.mesh).length

/-- The two CPU sequences in the funded proof are literally the local block of the
installed fixed-calendar program, with its original paid bank and the same clock. -/
theorem wide_local_installed (W : ℕ) (paid : Bank) :
    (l).localCode W paid=(ProcedureBank.program (WideCPU.Dated.last last)
      (fun i=>((real).sheets rom work i).code W)).seq ((terminal).code W paid) ∧
    (l).localTicks paid=(∑i,((real).sheets rom work i).ticks)+(terminal).ticks paid := ⟨rfl,rfl⟩

theorem wide_local_public_room :
    3*(real).romEnd rom+2≤work ∧
    v.wideTerminalROMEnd x.h x.w v.maxBits ((real).romEnd rom) ((real).workEnd work)≤work := by
  refine ⟨v.wide_dated_ballot_guard x m ell (v.wideInstalledCap unitCost) real v.maxBits rom,?_⟩
  apply (v.wide_terminal_before_groups x real v.maxBits rom ((real).workEnd work)).trans
  unfold wideInstalledSize wideFormatEnd wideFormatROM wideLayersROM
  exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
