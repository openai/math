import OAI.Hierarchy.ProbeFixedWideFundedAlignment
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueGeometry

namespace OAI
/-! # Length codes of every emitted funded pruning row -/
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
/-- All physical candidate slots are scanned, including dormant bought records. -/
def WideFundedLengthCodes {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    (cj : Columns h D × Fin k→ℕ) : Prop :=
  let archive:=result routes (result ((L).scans v.mesh num)
    (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
  let closed:=ReserveUse.output original old supply site debit archive
  let output:=(sink).terminalRows closed ord ci cj
  ∀j,(output j).lengthCode≤BoughtSockets.Public.maxMetric v.radius

set_option maxHeartbeats 1200000 in
theorem wide_funded_length_codes :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width bits size, v.wideFundedSize h width bits ≤ size →
      width≤2^h → v.keepLimit*width+1≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) {entries : ℕ}
        (site : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k)) (debit : Fin entries→ℕ)
        (cj : Columns h (2^v.W) × Fin k→ℕ),
        v.WideFundedLengthCodes h width size bits π raw site debit cj := by
  filter_upwards [v.wide_funded_core_reads,v.wide_funded_alignment,Filter.eventually_ge_atTop v.wideFundedHeight]
    with h cores frames tall
  intro width bits size extendsTape small budget π raw entries site debit cj j
  have coreRead := cores width bits size extendsTape small budget π raw site debit cj
  have boughtRead := (frames width bits size extendsTape small budget π raw site debit cj).2
  let placed := v.widePlacement h width
  let funds := v.fixedTerminalStock placed h width
  let ordering := wideRouteOrder h (2^v.W) k
  let tape := v.wideFundedRaw h width bits raw
  let current := v.wideSignedCheckoutAt h width size funds v.radius π ordering tape
  let wordBits := Native.wordBits h (2^v.W) Native.copies
  have word := (v.wide_signed_room h width funds (v.fixedTerminalStock_end placed h width)
    ((le_max_left ..).trans tall) budget).2
  have fits := (v.wide_funded_extent h width bits).trans extendsTape
  have mounted := (v.wide_funded_stock_at_size h width v.radius π raw bits size extendsTape tall budget small).mounted_all
  have actual := v.wide_core_checkout h width size fits funds v.radius π ordering tape word mounted
  rcases placed.catalogue.split_index j with ⟨i,rfl⟩|⟨i,rfl⟩
  · apply (coreRead i).lengthField.le.trans
    change (placed.catalogue.core.lengthCode.eval current (i.val:Word wordBits)).val≤_
    rw [(actual i).2.2.2.1]
    exact (Nat.mod_le _ _).trans (BoughtSockets.Public.coreCode_le v.sampler v.radius ((v.wideOrder h width) i))
  · apply (boughtRead i).lengthField.le.trans
    change 1≤BoughtSockets.Public.maxMetric v.radius
    unfold BoughtSockets.Public.maxMetric
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
