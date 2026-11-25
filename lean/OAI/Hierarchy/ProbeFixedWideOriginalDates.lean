import OAI.Hierarchy.ProbeFixedWideOriginalRolePages
import OAI.Hierarchy.ProbeFixedWideControlIssued
import OAI.Hierarchy.ProbeFixedWideSparseIssued
import OAI.Hierarchy.TaggedWideSparsePrefixImage
import OAI.Hierarchy.TaggedWideOriginalRevenue
import OAI.Hierarchy.TaggedWideTransportMask
import OAI.Hierarchy.TaggedWideWindowPorts

namespace OAI
/-! # One execution of all original physical date and width pages -/

noncomputable section
set_option quotPrecheck false
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
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw (v.maxBits) issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R» := WideMemory.R v.sampler h v.W k) v.sampler directory rows
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

def wideBallotHeight := Nat.find (Filter.eventually_atTop.1 v.wide_dated_ballot_issued)

include horizon age budget small operandAge card A₀
theorem wide_original_dates (m : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (activeAge : v.wideDatedSupportHeight≤h)
    (ballotAge : v.wideBallotHeight≤h) (nativeRadius : M=v.radius)
    (ell unitCost rom work : ℕ) (oldEnd : (v.wideReserveLayout h width ss).scratch≤work)
    (top : (A).endAddress v.mesh≤rom) (funded : full≤work)
    (gap : 3*(v.wideDated h width ell unitCost).romEnd rom+2≤work)
    (room : (v.wideDated h width ell unitCost).workEnd work<2^w)
    (headerSeed emittedInput : Memory w) (rendered : Fin rows→ProtocolRAMEmit.Row) (live : Fin rows→Bool)
    (rawFrame : ∀i,dst≤ i→i<dst+9*rows→m i=ProtocolRAMEmit.emitted dst rendered emittedInput i)
    (beforeROM : dst+6*rows+ProtocolRAMPurchaseSampler.span (3*rows)≤rom)
    (sources : ∀i,i<(A).endAddress v.mesh→m i=chk i)
    (header : ∀i, rom≤ i→i<(v.wideDated h width ell unitCost).romEnd rom→m i=
      (v.wideDated h width ell unitCost).words rom (SiteDirectory.table h D k) live headerSeed i) :
    let real:=v.wideDated h width ell unitCost
    ∃out,(ThreeFlat.RAM.ProcedureBank.program (WideCPU.Dated.last last)
      (fun i=>(real.sheets rom work i).code w)).Exec m out (∑i,(real.sheets rom work i).ticks) ∧
      (∀j:Fin (last+1),∀f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
        (real.roleStart work j) (value j.val ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) out f) ∧
      (∀i : Fin rows,(real.stageWidth work).read out ((3*i.val:ℕ):Word w)=
        ((if live i then (rendered i).width else 0:ℕ):Word w)) ∧
      (∀b,∀i : Fin rows,(real.slotBank work b).read out (i.val:Word w)=
        (real.lanes:Word w)*(real.orderedSlot b).eval m (i.val:Word w)) ∧ ∀a,a<work→ out a=m a := by
  intro real
  change 3*real.romEnd rom+2≤work at gap
  change real.workEnd work<2^w at room
  have mounted:=real.mounted_image rom (SiteDirectory.table h D k) live headerSeed m header
  have physicalImage : (v.wideDated h width ell unitCost).words rom (SiteDirectory.table h D k) live m = m := mounted
  have extent:=(v.wide_funded_extent h width bits).trans horizon
  have after : real.rolesEnd work≤real.workEnd work:=by
    dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf];omega
  have workFits : work<2^w:=((Nat.le_add_right ..).trans after).trans_lt room
  have romFits : rom+real.sites≤real.romEnd rom:=by
    dsimp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,WideCPU.Dated.firstROM,
      WideCPU.Dated.siteROM,WideCPU.endOf];omega
  have strideRoom : rom+ProtocolRAMPurchaseSampler.span siteCount≤work:=by
    have eq : real.sites=siteCount:=rfl
    have sz:=ProtocolRAMPurchaseSampler.span_le siteCount
    omega
  have siteRoom : siteCount≤2^w:=by have:=ProtocolRAMPurchaseSampler.lt_span siteCount;omega
  have rowsRoom : 3*rows≤2^w:=by have:=ProtocolRAMPurchaseSampler.lt_span (3*rows);omega
  have strideRead (i:Fin siteCount) : (real.siteStride rom).read m (i.val:Word w)=
      ((i.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w) := by
    have hit:=real.stride_mounted rom (SiteDirectory.table h D k) live m i
    rw [mounted] at hit
    change m (rom+(i.val:Word w).val%ProtocolRAMPurchaseSampler.span siteCount)=_
    rw [Fin.val_cast_of_lt (i.isLt.trans_le siteRoom),Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
    exact hit
  have roles:=v.wide_original_role_pages h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    m pages baseline keep cost highFit activeAge nativeRadius ell unitCost rom work funded oldEnd strideRoom strideRead (after.trans_lt room)
  let roleResultAt:=real.roleResult (native:=w) rom work v.sampler π v.depth marks unique names (fun j:Fin (last+1)=>value j.val ∘ embedded ∘ names)
    (fun i=>(sparse (names i)).val) (by rfl)
  apply real.original_run rom work roleResultAt (real.widthResult rom work live (fun i=>(rendered i).width))
    (fun b=>real.slotResult work b m) m roles
  · intro j
    cases markDate:(events v.mesh).get j with
    | attempt a=>
      have native:=(Nat.find_spec (Filter.eventually_atTop.1 v.wide_dated_ballot_issued)) h ballotAge width small budget
        size extent M π seed nativeRadius ell unitCost rom work live m sources top gap room j a markDate
      simpa only [physicalImage] using native
    | feed b=>
      have native:=v.wide_feed_ballot_issued h width ell unitCost rom work (SiteDirectory.table h D k) live m gap room j b markDate
      simpa only [physicalImage] using native
  · intro j
    have native:=v.wide_original_control_issued h width ell unitCost rom work (SiteDirectory.table h D k) live m gap room j
    simpa only [physicalImage] using native
  · apply real.width_issued rom work m live (fun i=>(rendered i).width)
    · intro i
      have hit:=real.mask_mounted rom (SiteDirectory.table h D k) live m i
      rw [mounted] at hit
      change m (real.maskROM rom+(i.val:Word w).val%ProtocolRAMPurchaseSampler.span rows)=_
      have iRow : i.val < rows := i.isLt
      rw [Fin.val_cast_of_lt (show i.val < 2^w by omega),
        Nat.mod_eq_of_lt (iRow.trans (ProtocolRAMPurchaseSampler.lt_span rows))]
      exact hit
    · exact WideCPU.measured_width real dst rendered m emittedInput rfl (ProtocolRAMPurchaseSampler.lt_span _).le rowsRoom rawFrame
    · change 0<ProtocolRAMPurchaseSampler.span (3*rows) ∧ ProtocolRAMPurchaseSampler.span (3*rows)<2^w ∧ dst+3*rows+1+ProtocolRAMPurchaseSampler.span (3*rows)≤work
      exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
    · have endFlag : real.maskROM rom+rows=real.romEnd rom:=rfl
      have pad:=ProtocolRAMPurchaseSampler.span_le rows
      change 0<ProtocolRAMPurchaseSampler.span rows ∧ ProtocolRAMPurchaseSampler.span rows<2^w ∧ real.maskROM rom+ProtocolRAMPurchaseSampler.span rows≤work
      exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
    · exact room
  · intro b
    exact real.slot_issued work b m (v.wideWindow_ordered_fits h width ell unitCost work funded workFits b) room

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
