import OAI.Hierarchy.ProtocolRAMCatalystSettledDirectory
import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeFixedWideCountedParents
import OAI.Hierarchy.ProbeFixedWideDatedAmounts

namespace OAI
/-! # Original report, price pages and input words after the counted native prefix -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



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


local notation "radius" => v.radius
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock radius π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "compile" => v.wideEventSlices h width bits
local notation "dest" => TerminalLayout.destination page
local notation "cj" => pairKeys (Columns h D) k

private theorem report_end_in_role : dest+9*rows ≤ full := by
  let z:=RoleRoom.shape («R»:=R) v.sampler directory rows
  have edge : rows < 2^page := by
    unfold wideSignedPage TerminalLayout.pageBits
    refine Nat.lt_of_le_of_lt ?_ Nat.lt_log2_self
    unfold TerminalLayout.footprint
    omega
  have base : 28*2^page ≤ hi := (le_max_left ..).trans (le_max_right ..)
  have stopped : hi ≤ z.stop hi := by
    simp only [RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,RoleRoom.Sizes.axis,
      RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  change 18*2^page+9*rows ≤ 3*(z.stop hi+1)
  omega

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size)
    (ready : CountedReady v h width v.maxBits)
    (accept : v.wideSignedCheckoutAt h width size
      (v.fixedTerminalStock (v.widePlacement h width) h width) v.radius π (wideRouteOrder h (2^v.W) k)
      (v.wideFundedRaw h width v.maxBits raw)
      ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)=0)
local notation "issuesOf" chartDates:arg => CatalystArchive.issued
  (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) chartDates
local notation "ownerOf" chartDates:arg positiveCount:arg =>
  CatalystArchive.nativeSite L v.mesh (issuesOf chartDates) positiveCount chk
local notation "debitsOf" chartDates:arg => CatalystArchive.debit v.mesh (issuesOf chartDates)
local notation "archive" => result routes (result ((L).scans v.mesh num)
  (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
local notation "reservedOut" owner:arg amount:arg => ReserveUse.output original old supply owner amount archive
local notation "settledOut" owner:arg amount:arg => (sink).output (reservedOut owner amount) ord ci (fun j=>(cj j).val)
local notation "locked" => (lw).bank last
local notation "endOfScan" => v.wideScanEnd h width ss (2^page)

include raw in
private theorem directory_of_counted_receipt {entries : ℕ}
    {owner : Fin entries → Fin num} {amount : Fin entries → ℕ}
    (m : Memory w) (receipt : Whole.Reconciliation sink original supply owner amount ord ci cj archive)
    (low : ∀j, j < full → m j=(settledOut owner amount) j) :
    ∃ key : Columns h D×Fin k→ℕ, RouteSettlement.Directory old m ord PurchaseInventory.slot key := by
  have count : rows < 2^page := by
    unfold wideSignedPage TerminalLayout.pageBits
    refine Nat.lt_of_le_of_lt ?_ Nat.lt_log2_self
    unfold TerminalLayout.footprint
    omega
  have kept (j : ℕ) (hj : j < 6*2^page) : m j=(settledOut owner amount) j := by
    apply low j
    have room:=v.report_end_in_role h width
    change 18*2^page+9*rows ≤ full at room
    omega
  refine ⟨fun j=>(cj j).val, ?_⟩
  exact TerminalLayout.settled_directory_at page start cnt supply (P).catalogue stock
    owner amount ord ci (fun j=>(cj j).val) archive m count.le receipt.ports.directory kept

private theorem arena_end_le_counted_page : (A).endAddress v.mesh ≤ 2^page := by
  have footprint : TerminalLayout.footprint v.mesh A stock stride rows r num cnt < 2^page := Nat.lt_log2_self
  unfold TerminalLayout.footprint at footprint
  omega

include raw in
/-- The original four route columns remain inside the preserved settlement
prefix at every later spill input. Their values include the actual signed permutation. -/
theorem wide_counted_directory {dates : Dates («w»:=w) C mid L pay num width} {pos : 0 < num}
    (m : Memory w)
    (receipt : Whole.Reconciliation sink original supply (ownerOf dates pos) (debitsOf dates) ord ci cj archive)
    (low : ∀j, j < full → m j=(settledOut (ownerOf dates pos) (debitsOf dates)) j) :
    ∃ key : Columns h D×Fin k→ℕ, RouteSettlement.Directory old m ord PurchaseInventory.slot key := by
  exact v.directory_of_counted_receipt h width size π raw m receipt low

include horizon ready raw in
/-- The readbacks refer to the actual numerical checkout used by the compact
CPU, including dormant original row ordinals in its published nine fields. -/
private theorem reached_inputs {entries : ℕ} {owner : Fin entries → Fin num} {amount : Fin entries → ℕ}
    (m : Memory w) (_receipt : Whole.Reconciliation sink original supply owner amount ord ci cj archive)
    (low : ∀j, j < full → m j=(settledOut owner amount) j)
    (widths : ∀j ≤ last,∀e : Fin rows,(m (((lw).bank j).base+e.val)).val=
      PaidWidths.total (PrefixWidths.prefixRows (events v.mesh) compile j) chk e) :
    (∀a, dest ≤ a → a < dest+9*rows → m a=ProtocolRAMEmit.emitted dest
      ((sink).terminalRows (reservedOut owner amount) ord ci (fun j=>(cj j).val))
      ((sink).terminalImage (reservedOut owner amount) ord ci (fun j=>(cj j).val)) a) ∧
    (∀a, a < (A).endAddress v.mesh → m a=chk a) ∧
    (∀i : Fin rows,(m ((locked).base+i.val)).val=PaidWidths.total ss chk i) := by
  have paid:=v.wide_funded_paid_at_size h width v.radius π raw bits size horizon ready.height ready.credit ready.size_le
  refine ⟨fun a _ ha=>(low a (ha.trans_le (v.report_end_in_role h width))).trans ?_,?_,?_⟩
  · exact congrFun ((sink).output_eq_emitted (reservedOut owner amount) ord ci (fun j=>(cj j).val)) a
  · intro a ha
    have prefixFit : a < 2^page := ha.trans_le (v.arena_end_le_counted_page h width)
    exact (low a (ha.trans_le (v.wide_funded_extent h width bits))).trans
      (TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride start cnt supply owner amount
        v.sampler v.wideJobs (routeBanks start cnt r) g ord ci (fun j=>(cj j).val) chk ss a rfl prefixFit paid)
  · intro i
    simpa only [PrefixWidths.prefixRows,List.take_length,v.wideEventSlices_flat] using widths last le_rfl i

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

open Lean Elab Term in
local elab "countedReadbackDates " cert:ident : term => do
  let proof ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType proof)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the prefix settlement reconciliation"
  let some recordRows := reconciliation.getAppArgs[7]? | throwError "expected the settlement record count"
  let count ← Meta.whnf recordRows
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issues ← Meta.whnf count.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issues.getAppArgs.back!

private theorem counted_page_room (rd : CountedReady v h width bits) :
    (lr).scratch + 2 * max (2^page) cnt < 2^w := by
  simpa only [wideScanEnd] using rd.ceiling

set_option maxHeartbeats 4000000 in
private abbrev counted_readback_pages (extent : v.wideFundedSize h width v.maxBits ≤ size)
    (conditions : CountedReady v h width v.maxBits)
    (approved : v.wideSignedCheckoutAt h width size
      (v.fixedTerminalStock (v.widePlacement h width) h width) v.radius π (wideRouteOrder h (2^v.W) k)
      (v.wideFundedRaw h width v.maxBits raw)
      ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)=0) :=
  let native:=CountedReady.execute (v:=v) (h:=h) (width:=width) («bits»:=bits) conditions size extent π raw 0 approved
  let certificates:=native.1.1.1.1
  let replay:=native.1.1.2
  let dates:=countedReadbackDates certificates
  let board:=mount
  let accounts : 0 < Fintype.card (Columns h D)*k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive
  v.wide_dated_pages_for_dates h width bits size v.radius π raw extent conditions.height
    conditions.credit conditions.size_le (dates:=dates) (pos:=accounts) (core:=board.ordinary) (center:=board.centers)
    (enum:=CoreRoute.enum board o) («ci»:=PurchaseInventory.slot) («cj»:=pairKeys (Columns h D) k)
    (2^page) (v.counted_page_room h width conditions) _ certificates replay.2.1 replay.2.2.1 replay.2.2.2

set_option maxHeartbeats 4000000 in
/-- A single accepted counted execution supplies the state used by the date
scatter and terminal turn, together with its original high input cells. -/
abbrev wide_counted_local_reads :=
  let native:=CountedReady.execute (v:=v) (h:=h) (width:=width) («bits»:=bits) ready size horizon π raw 0 accept
  let run:=native.1.1
  let replay:=run.2
  let receipt:=run.1
  let atCut:=v.reached_inputs h width size π raw horizon ready _ receipt.1 replay.2.1 replay.2.2.1
  let pages : v.WideDatedPages h width bits mid chk _ _ :=
    counted_readback_pages (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (raw:=raw)
      (extent:=horizon) (conditions:=ready) (approved:=accept)
  And.intro native.2.1 (And.intro receipt.1 (And.intro receipt.2.2.2
    (And.intro pages (And.intro replay.2.1 (And.intro atCut native.2.2)))))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
