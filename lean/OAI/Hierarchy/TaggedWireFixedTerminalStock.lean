import OAI.Hierarchy.TaggedWireFundedReport
import OAI.Hierarchy.TaggedWireWideGoodsChange

namespace OAI
/-! # Terminal goods in the original funded report and in the live role scan -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
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

attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages Sink.output Sink.terminalRows

set_option maxHeartbeats 2000000
include horizon age budget small

/-- The named output of the original route settlement reads the same stock
word as the signed calendar checkout at the chronological end of its run. -/
theorem wide_report_stock_at
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (i : Commodity (Fin (2^h)) N k) :
    let Z:=v.wide_report_at (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
      (bits:=bits) (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (issues:=issues)
      (who:=who) (cj:=cj) (marks:=marks) (A₀:=A₀) baseline read cost
    Z.stock i=(chk ((stock).base+PurchaseInventory.slot i)).val ∧
      Z.stock i=v.wireGoodsAt h width (events v.mesh).length (run C (events v.mesh) mid) i := by
  intro Z
  let j:=PurchaseInventory.slot i
  let span:=2^page
  have capacity:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  have wordRoom : 28*span<2^w:=capacity
  have sizeBound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<span:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at sizeBound
  have ok : j<(stock).size:=(PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _)
  have addr : (stock).base+j<(A).endAddress v.mesh:=
    (Nat.add_lt_add_left ok (stock).base).trans_le (v.fixedTerminalStock_end P h width)
  have first : (A).endAddress v.mesh<span:=by omega
  have word : j<2^w:=by omega
  have stored:=v.wide_funded_paid_at_size h width M π raw bits size horizon age budget small
  have file:=PaidWidths.frame (old).width rows (TerminalLayout.source page) ss chk ((stock).base+j)
    (fun t ht=>(stored t ht).1) (by change (stock).base+j<1*span;omega)
  have copy:=v.committed_prefix h width size M π seed who dur ss ((stock).base+j) (by omega)
  have paidStock : Z.stock i=(chk ((stock).base+j)).val:=by
    change ((stock).read closed (j:Word w)).val=_
    simp only [Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt ok]
    exact congrArg Fin.val (copy.trans file)
  exact ⟨paidStock,paidStock.trans (v.wire_terminal_goods h width mid i).symm⟩

include card in
/-- Every native turn read uses the same stock as the named funded report,
including when replay has extended the machine beyond the original paid shelf. -/
theorem wide_report_turn_stock
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (m : Memory w) (keep : ∀x,x<full→m x=settled x) (i : Commodity (Fin (2^h)) N k) :
    let Z:=v.wide_report_at (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
      (bits:=bits) (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (issues:=issues)
      (who:=who) (cj:=cj) (marks:=marks) (A₀:=A₀) baseline read cost
    ((stock).read m ((PurchaseInventory.slot i:ℕ):Word w)).val=Z.stock i := by
  intro Z
  have stored:=v.wide_report_stock_at (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (bits:=bits) (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (issues:=issues)
    (who:=who) (cj:=cj) (marks:=marks) (A₀:=A₀) baseline read cost i
  have inputs:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small card who dur ord
    ci (fun j=>(cj j).val) m keep
  have same:=inputs.2.2.2.2.2.2
  let j:=PurchaseInventory.slot i
  have ok : j<(stock).size:=(PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _)
  have addr : (stock).base+j<(A).endAddress v.mesh:=
    (Nat.add_lt_add_left ok (stock).base).trans_le (v.fixedTerminalStock_end P h width)
  have fit:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).2
  have word : j<2^w:=by omega
  change ((stock).read m (j:Word w)).val=_
  simp only [Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt ok]
  exact (congrArg Fin.val (same _ addr)).trans stored.1.symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
