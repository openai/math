import OAI.Hierarchy.ProbeFixedWideReportedWidth
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix

namespace OAI
/-! # The live old paid-width bit on each true original terminal row -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
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
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
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
local notation "mid" => Boot.booted market size (v.wideSignedWords h width stock M π o raw)
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw



local notation "place" => siteNumber h D k
local notation "mountedBoard" => (P).catalogue.coreMount π place (v.wideOrder h width) chk
local notation "ord" => CoreRoute.enum mountedBoard o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i

theorem wide_last_paid_le {n : ℕ} (owner : Fin n→Fin num) (dur : Fin n→ℕ) (cj : Columns h D × Fin k→Fin num)
    (bits : ℕ) (m : Boot.Tape h D)
    (physical : StockBound.Run C (v.stockBanks P h width) mid h N k (v.keepLimit*width))
    (wordRoom : 28*2^page<2^w) :
    let ss:=v.widePaidSlices h width bits
    let lw:=v.wideWidthLayout h width ss
    let kbank:=lw.bank last
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let committed:=ReserveUse.output original old supply owner dur archive
    PaidWidths.Mounted (old).width rows (TerminalLayout.source page) ss chk →
    (∀e : Fin rows,PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) →
    Whole.Reconciliation sink original supply owner dur ord ci cj archive →
    (∀e : Fin rows,(m (kbank.base+e.val)).val=PaidWidths.total ss chk e) →
      ∀e : Fin rows,(kbank.read m (e.val:Word w)).val≤((sink).terminalRows committed ord ci (fun j=>(cj j).val) e).width := by
  intro ss lw kbank archive committed stored cost originalRun lastPage e
  have bound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at bound
  have fit : e.val<2^w:=e.isLt.trans_le (by omega)
  have pageRoom : e.val<kbank.size := e.isLt.trans_le lw.covered
  change (m (kbank.base+(e.val:Word w).val%kbank.size)).val≤_
  rw [Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt pageRoom,lastPage]
  exact (v.wide_terminal_width_at h width size M π raw owner dur cj ss physical stored wordRoom cost originalRun e).2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
