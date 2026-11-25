import OAI.Hierarchy.ProbeFixedPaidFeedCells
import OAI.Hierarchy.ProbeFixedWideStockRun

namespace OAI
/-! # Live signed feed cells at their original fixed wide checkout -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
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


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


/-- The full protected forward feed has a word bound before the terminal flag
is read. The table, cap, and previous stock are those of the signed program. -/
theorem wide_paid_feed_stock (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h) :
    v.PaidFeedStock P h width r banks source table target owners
      (v.wideSignedMidAt h width size stock M π order raw) := by
  let m:=v.wideSignedMidAt h width size stock M π order raw
  have sizes:=v.wide_stock_sizes h width late budget small
  have inventory:=v.wide_stock_at h width size extent M π raw late budget small
  obtain ⟨_,_,_,econ,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π order raw sizes.words.addresses
  have pages:=v.wide_stock_pages h width size extent stock M π order raw r banks source table target owners
    sizes.roles sizes.alphabet sizes.copies sizes.mass econ
  exact ⟨inventory,rfl,rfl,small,dimension,sizes.words.addresses,⟨m,pages.1⟩⟩

theorem wide_paid_feed_cell (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (b : Boundary) (live : Event.feed b∈events v.mesh) (c : CommodityColumn)
    (column : c∈(FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit b).columns)
    (i : Fin c.rows) :
    ((v.wideSignedCheckoutAt h width size stock M π order raw) (c.overflow+i.val)).val≤(v.keepLimit+1)*width :=
  v.paid_feed_cell_of_stock P h width r banks source table target owners _
    (v.wide_paid_feed_stock h width size extent M π raw late budget small dimension) b live c column i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
