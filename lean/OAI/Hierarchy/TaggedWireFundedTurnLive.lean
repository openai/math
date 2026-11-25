import OAI.Hierarchy.TaggedWireWideTurnLive
import OAI.Hierarchy.TaggedWireFundedTurnCounters
import OAI.Hierarchy.TaggedWireLastPaidWidth
import OAI.Hierarchy.TaggedWireTurnOperandRoom

namespace OAI
/-! # The actual eleven live turn words of the funded wide CPU -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit WireTelescope ProtocolRAMEmit
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

/-- Alignment of the settled catalogue rows with the original purchased row identifiers. -/
abbrev WideFundedTurnAlignment :=
  Alignment (P).catalogue v.sampler π v.depth marks M rawRow counts
    ((P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks))

variable (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who cj marks)

attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages Sink.output Sink.terminalRows
  wideFundedSize wideSignedCheckoutAt wideSignedMidAt

include horizon age budget small operandAge card in
set_option maxHeartbeats 4000000 in
/-- The physical program and the exact live-width identities at the native
post-replay cut. All remaining input records are direct outputs of the single
calendar, its signed clock and the original paid-row alignment. -/
theorem wide_funded_turn_live (workStart : ℕ) (m : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (charged : ∀j : Fin num,RouteSettlement.actual (old).used closed j.val=
      usedAt (CatalystArchive.site v.mesh issues) dur j ∧ RouteSettlement.actual (old).reserved closed j.val=supply)
    (keep : ∀x,x<full→m x=settled x)
    (lastRead : ∀e : Fin rows,(m (((lw).bank last).base+e.val)).val=PaidWidths.total ss chk e)
    (cost : ∀e : Fin rows,PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (afterReplay : v.wideReplayedTurnBase h width ss≤workStart)
    (room : workStart+7*Fintype.card (Old h v.W k rows)+4*rows<2^w) :
    let lastBank := (lw).bank (events v.mesh).length
    let turn := RoleRoom.turnBoard («R»:=R) v.sampler directory (edges:=rows) hi workStart
      (P).catalogue.core (v.widePaidPorts h width hi)
    let inventory := Inventory.ofOriginal ((RoleRoom.shape («R»:=R) v.sampler directory rows).stop hi) (Fintype.card (Old h v.W k rows)) lastBank
      stock (old).reserved (old).used
    let fixed := fun e : Fin rows => (lastBank.read m (e.val:Word w)).val
    let goods := fun i : Goods h v.W k => ((stock).read m ((PurchaseInventory.slot i:ℕ):Word w)).val
    let amounts := SettledMatrix.Layout.bits fixed goods (fun _ : Catalysts h v.W k => supply)
      (RoleRoom.usedBy v.mesh issues)
    let ports := livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
    let before := fun (i : Fin (Fintype.card (Old h v.W k rows))) (_ : 0<amounts i) side =>
      publicRoleFor v.sampler π (activePaid v.sampler counts ports) (SettledMatrix.Layout.numbered i) side
    (turn.extended inventory w).Exec m (turn.extendedState inventory m) (turn.extendedTime inventory) ∧
      Board.LiveReads v.sampler turn amounts counts before (fun i pos side => .inl (ports i pos side))
        (turn.extendedState inventory m) := by
  let inputs:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small (entries:=recordCount v.mesh issues) card who dur
    (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k)
    (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun j=>(cj j).val) m
    (by intro addr below; with_reducible exact keep addr below)
  let physical:=v.wide_funded_stock_at_size h width M π raw bits size horizon age budget small
  let stored:=v.wide_funded_paid_at_size h width M π raw bits size horizon age budget small
  let capacity:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans age) budget
  let money:=v.wide_last_paid_le h width size M π seed who dur cj bits m
    (by simpa only [wideSignedMidAt] using physical) capacity.1 stored cost baseline lastRead
  let spent:=v.wide_turn_counters h width size M π raw bits who dur (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun j=>(cj j).val)
    (usedAt (CatalystArchive.site v.mesh issues) dur) m keep charged
  let sizes:=v.wide_operand_room h width operandAge capacity.2
  exact v.wide_signed_turn_live_at h width ss workStart M π marks unique A₀ m inputs.1 inputs.2.1 inputs.2.2.1
    inputs.2.2.2.2.1 inputs.2.2.2.1 (fun e=>inputs.2.2.2.2.2.1 e.1 _) issues spent money
    afterReplay room sizes.1 sizes.2.1 sizes.2.2.1 sizes.2.2.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
