import OAI.Hierarchy.ProbeFixedWideBoughtSupport
import OAI.Hierarchy.ProbeFixedWideCoreCheckout
import OAI.Hierarchy.ProbeFixedWideBoughtCatalogue
import OAI.Hierarchy.ProbeFixedWideHistorySupported
import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProtocolRAMCatalogueCheckout
import OAI.Hierarchy.ProtocolRAMCatalogueInjection
import OAI.Hierarchy.ProtocolRAMCoreCatalogueLocated

namespace OAI
/-! # Positive original catalogue identifiers on the funded wide terminal -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
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

variable (size bits : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
local notation "place" => siteNumber h D k
local notation "mountedBoard" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mountedBoard o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "ss" => v.widePaidSlices h width bits
local notation "full" => v.wideFundedSize h width bits
local notation "marks" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
local notation "acquired" => fun e : Bought v.sampler π v.depth marks=>
  (((P).routes.directory).header h D k v.sampler.degree v.depth).enum ⟨e.1,BoughtLocation.relative e.2⟩

/-- The port-header ordering is the original purchased catalogue ordinal
used by the public profile and paid-slice accounting. -/
theorem wide_funded_original :
    (P).catalogue.original v.sampler π v.depth marks order acquired=
    ⇑((P).catalogue.ordinal v.sampler π v.depth marks order rfl) := by
  funext e
  cases e <;> rfl

/-- Both views refer to the same permanent socket and dated acquired record. -/
def WideFundedAlignment {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  Nonempty (Alignment (P).catalogue v.sampler π v.depth marks v.radius output (fun i=>(output i).width)
    ((P).catalogue.original v.sampler π v.depth marks order acquired)) ∧
    ∀ j : Fin (P).catalogue.boughtRows, Reads (output ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val)

/-- Each economic row reports its own original absolute link identifier. -/
def WideFundedRowIds {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  ∀j,(output j).link=j.val

/-- The six permanent-row fields at the serializer refer to the earlier checkout. -/
def WideFundedCoreReads {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  ∀j : Fin (P).catalogue.coreRows, Reads (output ((P).catalogue.coreIndex j))
    ((P).catalogue.core.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.coreIndex j).val)

private theorem funded_alignment_at (extent : full ≤ size) (height : v.wideFundedHeight≤h)
    (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (space : siteLast h D k+1≤2^w ∧ (P).catalogue.idBase+rows<2^w ∧
      ∀j,coreCode v.sampler v.radius ((order) j)<2^w)
    (support : v.WideHistorySupport h width chk bits)
    (bought : v.WideBoughtCatalogue h width size π seed)
    {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D × Fin k→ℕ) :
    v.WideFundedAlignment h width size bits π raw site debit cj ∧ v.WideFundedRowIds h width size bits π raw site debit cj ∧
      v.WideFundedCoreReads h width size bits π raw site debit cj := by
  have run:=v.wide_funded_stock_at_size h width v.radius π raw bits size extent height budget small
  have paid:=v.wide_funded_paid_at_size h width v.radius π raw bits size extent height budget small
  have initial:= (v.wide_funded_extent h width bits).trans extent
  have room:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans height) budget).1
  have geo:=v.wide_geometry_at_page h width stock stride start num cnt room
  have ready:=TerminalLayout.allocated v.mesh A L (P).catalogue h v.W k num cnt start stride w stock rfl
    (v.catalyst_static_end P h width A).le geo room
  have core:=v.wide_core_checkout h width size initial stock v.radius π o seed
    ((Nat.le_add_right ..).trans_lt ready.flagWord) run.mounted_all
  have sold : ∀z∈ss,(P).catalogue.Supported z chk := by
    intro z hz
    rw [←v.wideEventSlices_flat h width bits] at hz
    obtain ⟨ev,earlier,kept⟩:=List.mem_flatMap.mp hz
    exact support ev earlier z kept
  have installed:=fun z hz=>(paid z hz).1
  have active:=v.wide_bought_activated h width size v.radius π seed site debit cj ss sold installed room
  have actualBought:=ready.bought_read v.sampler g v.wideJobs supply site debit ss chk installed
    (fun f _=>geo f) space.2.1 ord ci cj
  have actualCore:=ready.core_read v.sampler g v.wideJobs supply site debit ss chk installed
    (fun f _=>geo f) space.2.1 ord ci cj
  constructor
  · exact ⟨⟨(P).catalogue.reportAlignment _ chk v.sampler π v.depth marks v.radius _ order acquired
    actualCore actualBought (fun j=>core.located v.depth marks j space.1 (space.2.2 j)) active
    (fun j hit=>(bought j).mp hit)⟩,actualBought⟩

  · refine ⟨?_,actualCore⟩
    have id_at (j : Fin rows) : (P).catalogue.idBase+j.val=j.val := Nat.zero_add _
    intro j
    rcases (P).catalogue.split_index j with ⟨i,rfl⟩|⟨i,rfl⟩
    · exact (actualCore i).link.trans (id_at _)
    · exact (actualBought i).link.trans (id_at _)

/-- The dated flags, physical column tables and true support of every event
slice produce the whole positive alignment on every sufficiently large height. -/
private theorem funded_row_data :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedAlignment h width size bits π raw site debit cj ∧ v.WideFundedRowIds h width size bits π raw site debit cj ∧
      v.WideFundedCoreReads h width size bits π raw site debit cj := by
  filter_upwards [v.wide_alignment_room,v.wide_history_supported,v.wide_bought_catalogue,
    Filter.eventually_ge_atTop v.wideFundedHeight] with h space support acquiredRows tall
  intro width bits size extent small budget π raw entries site debit cj
  let tape:=v.wideFundedRaw h width bits raw
  have fits:=(v.wide_funded_extent h width bits).trans extent
  exact v.funded_alignment_at h width size bits π raw extent tall small budget (space width)
    ((support width small budget size fits π tape bits).2)
    (acquiredRows width small budget size fits π tape) site debit cj

theorem wide_funded_alignment :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedAlignment h width size bits π raw site debit cj := by
  filter_upwards [v.funded_row_data] with h rowsAt
  intro width bits size extent small budget π raw entries site debit cj
  exact (rowsAt width bits size extent small budget π raw site debit cj).1

theorem wide_funded_row_ids :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedRowIds h width size bits π raw site debit cj := by
  filter_upwards [v.funded_row_data] with h rowsAt
  intro width bits size extent small budget π raw entries site debit cj
  exact (rowsAt width bits size extent small budget π raw site debit cj).2.1

theorem wide_funded_core_reads :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedCoreReads h width size bits π raw site debit cj := by
  filter_upwards [v.funded_row_data] with h rowsAt
  intro width bits size extent small budget π raw entries site debit cj
  exact (rowsAt width bits size extent small budget π raw site debit cj).2.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
