import OAI.Hierarchy.ProbeFixedWideFundedAlignment
import OAI.Hierarchy.TaggedWireWidePaidCoordinates
import OAI.Hierarchy.TaggedWireWidePaidShelf

namespace OAI
/-! # Actual group owners of both sides of the funded native reporter -/
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

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

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

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K
  (directory).groups H (WideMemory.R v.sampler h v.W k)
local notation "originalRow" => (P).catalogue.original v.sampler π v.depth marks order acquired
local notation "lab" => HistoryRoles.labelled v.sampler π v.depth marks
local notation "win" => (fun _ : Fin rows=>0)

/-- The actual group word of the original paid catalogue record on the emitted terminal. -/
def WideFundedGroupTable {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  ∀(unique : Exclusive marks) (j : ReportSockets.Row v.sampler π v.depth marks),
    (output ((originalRow) ((lab).symm (.inr j)))).group=
      (ReportSockets.placed v.sampler π v.depth marks unique directory (j,false)).1.val

/-- On either orientation of a positive emitted row, the packed geometric
socket's owner is the emitted group ordinal used by the frozen window. -/
def WideFundedOwners {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  ∀(unique : Exclusive marks)
    (receipt : Alignment (P).catalogue v.sampler π v.depth marks v.radius output (fun j=>(output j).width) originalRow)
    (hw : 0<width),
    let anchor := (CatalogueRows.Alignment.location v.sampler π v.depth marks unique (P).catalogue order acquired output
      receipt win 0 width hw).trans (ReportSockets.packed directory)
    ∀i side,(anchor (i,side)).1.val=(output i.val).group

private theorem funded_group_table_at {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) (extendsTape : full ≤ size) (small : width≤2^h)
    (budget : v.keepLimit*width+1≤2^h) (tall : v.wideFundedHeight≤h)
    (strip : v.stripHeight≤h) (dates : v.wideJobs≤h)
    (reads : v.WideFundedCoreReads h width size bits π raw site debit cj)
    (frame : v.WideFundedAlignment h width size bits π raw site debit cj) :
    v.WideFundedGroupTable h width size bits π raw site debit cj := by
  have bought := frame.2
  have word := (v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans tall) budget).2
  have fits := (v.wide_funded_extent h width bits).trans extendsTape
  have mounted := (v.wide_funded_stock_at_size h width v.radius π raw bits size extendsTape tall budget small).mounted_all
  have boot := v.wide_signed_boot_at h width size fits stock v.radius π o seed word
  have low := (v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have first : (A).first≤(A).endAddress v.mesh := Nat.le_add_right ..
  have seen := boot.2.2.1.frame (low.trans_lt (first.trans_lt word))
    (fun x hx=>v.wide_signed_checkout_below h width stock v.radius π o seed size x (hx.trans_le low) mounted)
  have shelves := v.wide_paid_shelf_read h width size fits v.radius π seed chk word mounted (fun _ _=>rfl)
  have tables := v.purchased_table_room h strip
  have jobs : v.wideJobs≤2^w := dates.trans ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)
  intro unique j
  refine CatalogueRows.Alignment.table_group v.sampler π v.depth marks unique (P).catalogue order acquired _
    directory chk seen.board.columns.groupFit seen.board.rows (fun a=>(reads a).group)
    (fun a=>(bought a).group) ?_ j
  intro e
  exact CatalogueRows.Alignment.bought_group v.sampler π v.depth marks unique (P).catalogue acquired
    directory chk published rfl (fun e=>v.wide_bought_coordinates h width v.radius π marks unique chk seen
      (fun e=>shelves e.1 (BoughtLocation.keyOf e.2)) jobs tables.1 tables.2.1 e false) e

private theorem funded_group_owners_at {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ)
    (groups : v.WideFundedGroupTable h width size bits π raw site debit cj) :
    v.WideFundedOwners h width size bits π raw site debit cj := by
  intro unique receipt hw
  exact CatalogueRows.Alignment.owner_of_table v.sampler π v.depth marks unique (P).catalogue order acquired _
    receipt directory win 0 width hw (groups unique)

theorem wide_funded_report_groups :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedGroupTable h width size bits π raw site debit cj := by
  filter_upwards [v.wide_funded_core_reads,v.wide_funded_alignment,Filter.eventually_ge_atTop v.wideFundedHeight,
    Filter.eventually_ge_atTop v.stripHeight,Filter.eventually_ge_atTop v.wideJobs] with h cores frames tall strip dates
  intro width bits size extendsTape small budget π raw entries site debit cj
  exact v.funded_group_table_at h width size bits π raw site debit cj extendsTape small budget tall strip dates
    (cores width bits size extendsTape small budget π raw site debit cj) (frames width bits size extendsTape small budget π raw site debit cj)

theorem wideWindow_owner_of_table :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedOwners h width size bits π raw site debit cj := by
  filter_upwards [v.wide_funded_report_groups] with h groupsAt
  intro width bits size extendsTape small budget π raw entries site debit cj
  exact v.funded_group_owners_at h width size bits π raw site debit cj
    (groupsAt width bits size extendsTape small budget π raw site debit cj)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
