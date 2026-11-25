import OAI.Hierarchy.ProbeFixedSharpPaidRows
import OAI.Hierarchy.ProbeFixedWideReportedWidth
import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.TaggedWireFundedReport

namespace OAI
/-! # Sharp original width of the rows printed in an installed window -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
set_option maxRecDepth 8192
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


local notation "place" => siteNumber h D k
local notation "ss" => v.widePaidSlices h width v.maxBits
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width v.maxBits raw
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

/-- The input to the window is the row of the actual settlement on the funded,
signed tape. This includes every original row, even unused sockets of width zero. -/
def PrintedWindowCapAt (unitCost : ℕ) : Prop :=
  chk ((A).endAddress v.mesh)=0 →
  ∀ {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D×Fin k→Fin num),
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let closed:=ReserveUse.output original old supply site debit archive
    let rawRow:=(sink).terminalRows closed ord ci (fun j=>(cj j).val)
    ∀j, (Tagged.WideStack.atScale ((P).catalogue.transport order) (fun _=>0) 0 rawRow j).width≤
      v.wideInstalledCap unitCost*width

/-- The input to the window is the row of the actual settlement on the funded,
signed tape. This includes every original row, even unused sockets of width zero. -/
def RawWindowCapAt (unitCost : ℕ) : Prop :=
  chk ((A).endAddress v.mesh)=0 →
  ∀ {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D×Fin k→Fin num),
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let closed:=ReserveUse.output original old supply site debit archive
    let rawRow:=(sink).terminalRows closed ord ci (fun j=>(cj j).val)
    ∀j, (rawRow j).width≤
      v.wideInstalledCap unitCost*width

/-- The original private tape uses the selected tariff times the payload width. -/
def PrivateWindowCapAt (unitCost : ℕ) : Prop :=
  chk ((A).endAddress v.mesh)=0 →
  ∀ {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D×Fin k→Fin num),
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let closed:=ReserveUse.output original old supply site debit archive
    let rawRow:=(sink).terminalRows closed ord ci (fun j=>(cj j).val)
    ∀j, (rawRow j).width≤
      v.widePrivateUnit unitCost*width

/-- The two bounds use the same settled row before and after its scale test. -/
def JointWindowCapAt (unitCost : ℕ) : Prop :=
  chk ((A).endAddress v.mesh)=0 →
  ∀ {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D×Fin k→Fin num),
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let closed:=ReserveUse.output original old supply site debit archive
    let rawRow:=(sink).terminalRows closed ord ci (fun j=>(cj j).val)
    ∀j, (rawRow j).width≤v.widePrivateUnit unitCost*width ∧
       (Tagged.WideStack.atScale ((P).catalogue.transport order) (fun _=>0) 0 rawRow j).width≤
      v.wideInstalledCap unitCost*width

set_option maxHeartbeats 1200000 in
private theorem jointWindowCap_at (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (horizon : v.wideFundedSize h width v.maxBits≤ size) (age : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (price : chk ((A).endAddress v.mesh)=0 → ∀ev∈events v.mesh,∀e : Fin rows,
      PaidWidths.total (v.wideEventSlices h width v.maxBits ev) chk e≤v.sharpPaidUnit*width)
    (room : chk ((A).endAddress v.mesh)=0 → ∀e : Fin rows,
      PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    v.JointWindowCapAt h width size π raw unitCost := by
  intro good entries site debit cj certificate closed rawRow e
  let paid:=PaidWidths.total ss chk e
  have stockInput:=v.wide_funded_stock_at_size h width v.radius π raw v.maxBits size horizon age budget small
  have paidInput:=v.wide_funded_paid_at_size h width v.radius π raw v.maxBits size horizon age budget small
  have word:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  have invoiceBound:=(v.wide_terminal_width_invoice h width size v.radius π seed site debit cj ss
    stockInput paidInput word (room good) certificate e).2.2
  have hist:=paid_history_prefix v.mesh (v.wideEventSlices h width v.maxBits) chk e
    v.sharpPaidUnit width last (fun ev hi=>price good ev hi e)
  simp only [List.take_length] at hist
  have period : paid≤HistoryRoles.clock v.mesh*unitCost*width:=
    hist.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ rate))
  have factor : v.overflowFactor v.keepLimit≤v.overflowFactor (2*v.keepLimit+1) :=
    Nat.mul_le_mul_left _ (by omega)
  have head : (HistoryRoles.clock v.mesh*unitCost+(v.overflowFactor v.keepLimit+fuel v.mesh))*width≤
      v.widePrivateUnit unitCost*width := by
    apply Nat.mul_le_mul_right
    change HistoryRoles.clock v.mesh*unitCost+(v.overflowFactor v.keepLimit+fuel v.mesh)≤
      HistoryRoles.clock v.mesh*unitCost+v.overflowFactor (2*v.keepLimit+1)+fuel v.mesh
    omega
  have actual : (rawRow e).width≤v.widePrivateUnit unitCost*width := calc
    _ ≤ paid+(v.overflowFactor v.keepLimit+fuel v.mesh)*width:=invoiceBound
    _ ≤ HistoryRoles.clock v.mesh*unitCost*width+(v.overflowFactor v.keepLimit+fuel v.mesh)*width:=
      Nat.add_le_add_right period _
    _ = _ := (Nat.add_mul ..).symm
    _ ≤ _ := head
  refine ⟨actual,?_⟩
  change (if (P).catalogue.transport order e ∧ (0:ℕ)=0 then (rawRow e).width else 0)≤_
  split
  · exact actual.trans (Nat.mul_le_mul_right width (Nat.le_succ _))
  · exact Nat.zero_le _

theorem printedWindowCap_at (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (horizon : v.wideFundedSize h width v.maxBits≤ size) (age : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (price : chk ((A).endAddress v.mesh)=0 → ∀ev∈events v.mesh,∀e : Fin rows,
      PaidWidths.total (v.wideEventSlices h width v.maxBits ev) chk e≤v.sharpPaidUnit*width)
    (room : chk ((A).endAddress v.mesh)=0 → ∀e : Fin rows,
      PaidWidths.total ss chk e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    v.PrintedWindowCapAt h width size π raw unitCost := by
  intro good n site debit cj base closed rawRow j
  exact (v.jointWindowCap_at h width size π raw unitCost rate horizon age budget small price room
    good site debit cj base j).2

/-- A fixed calibrated amount works for every allowed parent and for all its
funded original calendars, permutations, tapes and settlement receipts. -/
private theorem window_complete_cap {κ B : ℝ} (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      ∀size, v.wideFundedSize x.h x.w v.maxBits≤ size →
      ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
        v.JointWindowCapAt x.h x.w size π raw unitCost := by
  have height : Filter.Tendsto (Tagged.WideParent.h (κ:=κ) («A»:=B)) (Tagged.WideParent.large κ B) Filter.atTop:=
    Filter.tendsto_comap
  filter_upwards [v.cofinal_terminal_bill (κ:=κ) (B:=B) v.maxBits,height.eventually v.wide_sharp_paid_rows,
    height.eventually (Filter.eventually_ge_atTop v.wideFundedHeight),
    height.eventually (Filter.eventually_ge_atTop v.widthFloor),
    Tagged.WideParent.fixed_mul_width (κ:=κ) («A»:=B) 1,
    Tagged.WideParent.fixed_mul_width (κ:=κ) («A»:=B) v.keepLimit] with x words rates late floor small budget
  have narrow : x.w≤2^x.h := by simpa only [one_mul] using (Nat.le_succ _).trans small
  intro size horizon π raw
  have extent:=(v.wide_funded_extent x.h x.w v.maxBits).trans horizon
  have native:=rates x.w narrow (floor.trans x.property.1.2.1) budget size extent π
    (v.wideFundedRaw x.h x.w v.maxBits raw)
  exact v.jointWindowCap_at x.h x.w size π raw unitCost rate horizon late budget narrow native
    (words size extent π (v.wideFundedRaw x.h x.w v.maxBits raw))

/-- A fixed calibrated amount works for every allowed parent and for all its
funded original calendars, permutations, tapes and settlement receipts. -/
theorem wideWindow_printed_cap {κ B : ℝ} (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      ∀size, v.wideFundedSize x.h x.w v.maxBits≤ size →
      ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
        v.PrintedWindowCapAt x.h x.w size π raw unitCost := by
  filter_upwards [v.window_complete_cap (κ:=κ) (B:=B) unitCost rate] with x bill
  intro size full π raw good n site debit cj base closed rawRow e
  exact (bill size full π raw good site debit cj base e).2

/-- A fixed calibrated amount works for every allowed parent and for all its
funded original calendars, permutations, tapes and settlement receipts. -/
theorem wideWindow_private_cap {κ B : ℝ} (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      ∀size, v.wideFundedSize x.h x.w v.maxBits≤ size →
      ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
        v.PrivateWindowCapAt x.h x.w size π raw unitCost := by
  filter_upwards [v.window_complete_cap (κ:=κ) (B:=B) unitCost rate] with x bill
  intro size full π raw good n site debit cj base closed rawRow e
  exact (bill size full π raw good site debit cj base e).1

theorem wideWindow_raw_cap {κ B : ℝ} (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      ∀size, v.wideFundedSize x.h x.w v.maxBits≤ size →
      ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
        v.RawWindowCapAt x.h x.w size π raw unitCost := by
  filter_upwards [v.window_complete_cap (κ:=κ) (B:=B) unitCost rate] with x bill
  intro size full π raw good n site debit cj base closed rawRow e
  exact (bill size full π raw good site debit cj base e).1.trans (Nat.mul_le_mul_right x.w (Nat.le_succ _))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
