import OAI.Hierarchy.TaggedWideDatedReportGraph
import OAI.Hierarchy.TaggedWireNativeReport
import OAI.Hierarchy.ProbeFixedWideDatedSheetReads
import OAI.Hierarchy.ProbeFixedDatedWireLedger

namespace OAI
/-! # Sparse native dates give the exact original public bit rows -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
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


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
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

local notation "pair" => pairKeys (Columns h D) k
private abbrev reportCost :=
  ∀e : Fin rows, PaidWidths.total ss chk e + (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : reportCost v h width size π raw bits)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
private abbrev reportDates := Dates C mid L pay num width

variable {dates : reportDates v h width size π raw bits} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
private def reportEntries (entries : reportDates v h width size π raw bits) : Attempt → Entry num width :=
  CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay)
    (count := num) (payload := width) entries
local notation "issues" => reportEntries v h width size π raw bits dates

private def reportSites (entries : reportDates v h width size π raw bits) (positive : 0 < num) :
    Fin (recordCount (count := num) (payload := width) v.mesh (reportEntries v h width size π raw bits entries)) → Fin num :=
  CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh
    (reportEntries v h width size π raw bits entries) positive chk
local notation "who" => reportSites v h width size π raw bits dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

local notation "cardFit" => v.wide_dated_bought_rows h width
local notation "names" => timeRows v.sampler π v.depth days (P).catalogue order cardFit pair
local notation "emb" => DatedRows.embed v.sampler π v.depth days (P).catalogue order cardFit
local notation "catalog" => (P).catalogue.ordinal v.sampler π v.depth days order cardFit
local notation "whereAt" => HistoryRoles.sorted v.sampler π v.depth days
local notation "V" => v.wideDatedValue h width bits mid chk issues

include horizon age budget small cost

/-- This equality uses the measured endpoint of the original terminal reporter
only when the amount already accumulated by the earlier date is positive. -/
theorem wide_numbered_date (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val)) (j : ℕ) :
    installedWidths (whereAt ∘ names) (V j ∘ emb ∘ names)=v.wideDatedWire h width bits π mid chk issues j := by
  let Z:=v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates := dates) (pos := pos) receipt funded
  let align:=funded.1.some
  let cash : Fin rows→ℕ:=fun e=>V j (.inl e)
  let goods:=fun i : Goods h v.W k=>V j (.inr (.inl i))
  let reserves:=fun a : Catalysts h v.W k=>V j (.inr (.inr a))
  have prior (i:Fin rows) : cash i≤Z.fixed i := by
    have bound:=PrefixWidths.prefix_total_le (events v.mesh) (v.wideEventSlices h width bits) chk j i
    rw [v.wideEventSlices_flat] at bound
    exact bound
  have source (e) : catalog (align.ident e)=e.val :=
    (v.wide_dated_original_ordinal h width π days _).symm.trans (align.original e)
  have agg:=Z.prefix_named_widths v.depth days names catalog align.ident source align.joins cash goods reserves prior
  have table : V j ∘ emb ∘ names=Sum.elim (cash ∘ catalog) (Sum.elim goods reserves) ∘ names := by
    funext i
    rcases origin:names i with e|good|a <;> simp only [Function.comp_apply,origin] <;> rfl
  rw [table]
  exact agg

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
