import OAI.Hierarchy.TaggedWireNativeReportStock
import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.TaggedWireSettledLayout

namespace OAI
/-! # The last chronological named amounts of the actual funded terminal report -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
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
private theorem finalValueOfAccounts (dates : Dates C mid L pay num width)
    (stocked : Commodity (Fin (2^h)) N k → ℕ) (reserved used : Columns h D × Fin k → ℕ)
    (stockEntry : ∀ i, stocked i = v.wireGoodsAt h width last (run C (events v.mesh) mid) i)
    (reserveEntry : ∀ i, reserved i = supply ∧ used i = v.wireUsedAt h width last (run C (events v.mesh) mid) i)
    (ready : Calendar.mounted C (events v.mesh) mid) (word : (A).endAddress v.mesh < 2^w)
    (countFits : num < 2^w) (widthFits : width < 2^w) :
    v.wideDatedValue h width bits mid chk (CatalystArchive.issued (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) dates) last =
      SettledMatrix.Layout.available (PaidWidths.total ss chk) stocked reserved used := by
  have atEnd : StockBound.state C mid last=run C (events v.mesh) mid := by
    change run C ((events v.mesh).take (events v.mesh).length) mid=_
    rw [List.take_length]
  funext e
  rcases e with e | i
  · change PaidWidths.total (PrefixWidths.prefixRows (events v.mesh) (v.wideEventSlices h width bits)
      last) chk e=PaidWidths.total ss chk e
    rw [PrefixWidths.prefixRows,List.take_length,v.wideEventSlices_flat]
  rcases i with i | i
  · have paid := stockEntry i
    rw [← atEnd] at paid
    exact (v.wire_goods_run h width last mid i).symm.trans paid.symm
  · obtain ⟨reserveEq,usedEq⟩ := reserveEntry i
    have balance := v.wire_countAt h width mid ready word countFits widthFits dates last le_rfl i
    rw [atEnd] at balance
    change supply-PrefixReserve.used (CatalystArchive.site v.mesh (CatalystArchive.issued (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) dates)) (CatalystArchive.debit v.mesh (CatalystArchive.issued (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) dates))
      (PrefixReserve.countAt v.mesh (CatalystArchive.issued (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) dates) last) (pair i)=reserved i-used i
    rw [reserveEq]
    exact congrArg (fun x => supply-x) (balance.symm.trans usedEq.symm)

attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

private abbrev finalDatedConclusion
    (state : Word w)
    (align : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
      v.WideFundedAlignment h width size bits π raw owner fees (fun z=>(pair z).val))
    (dates : Dates C mid L pay num width) : Prop :=
    let Z:=v.wide_native_report h width size π raw bits horizon age budget small cost state align
    v.wideDatedValue h width bits mid chk (CatalystArchive.issued (chart:=C) (initial:=mid) («L»:=L) (base:=pay) (count:=num) (payload:=width) dates) last =
      SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used

/-- The signed report and the final dated value assign the same integer to every
original paid edge, commodity, and catalyst pair. -/
theorem wide_final_dated_value
    (state : Word w)
    (align : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
      v.WideFundedAlignment h width size bits π raw owner fees (fun z=>(pair z).val))
    (dates : Dates C mid L pay num width) :
    finalDatedConclusion v h width size π raw bits horizon age budget small cost state align dates := by
  unfold finalDatedConclusion
  intro Z
  have whole := (v.wide_funded_stock_at_size h width v.radius π raw bits size horizon age budget small).mounted_all
  have word := (v.wide_stock_sizes h width ((le_max_right ..).trans age) budget small).words.addresses
  have capacity := (v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  have pageRoom : 28*2^page < 2^w := capacity
  let runWitness := v.wide_funded_run_at h width v.radius π raw bits size horizon age budget small state
  let charged := Classical.choose_spec runWitness
  have countRoom : num ≤ 2^page := charged.1.usedSize
  apply finalValueOfAccounts v h width size π raw bits dates Z.stock Z.reserved Z.used _ _ whole word
    (by omega) (small.trans_lt (v.date_prefix_fit h))
  · intro i
    exact (v.wide_native_report_stock h width size π raw bits horizon age budget small cost state align i).2
  · intro i
    have paid := v.wide_native_report_reserve h width size π raw bits horizon age budget small cost state align i
    exact ⟨paid.1,paid.2.2⟩
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
