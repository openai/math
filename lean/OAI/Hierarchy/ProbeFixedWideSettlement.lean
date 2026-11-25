import OAI.Hierarchy.ProbeFixedWideWordRoom
import OAI.Hierarchy.ProbeFixedWideSettlementPage
import OAI.Hierarchy.ProbeFixedCatalystClosed
import OAI.Hierarchy.ProbeFixedCatalystMarkets
import OAI.Hierarchy.ProbeFixedTerminalStock
import OAI.Hierarchy.ProbeFixedPostprocessing
import OAI.Hierarchy.ProbeFixedWideGeometry
import OAI.Hierarchy.ProtocolRAMCatalogueMount
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.ProtocolRAMCatalystTerminalScale
import OAI.Hierarchy.TaggedWideNativeArena

namespace OAI
/-! # Fixed settlement on the original public placement and its own purchased endpoint records -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h

local notation "page" => v.wideSignedPage h width

/-- Genuine CT, original marked-row sources, signed role register, and two compact
policy charge catalogues in the initial memory read by the hardware. -/
def wideSignedWords (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) : Boot.Tape h D :=
  let bits:=page stock
  let own:=TerminalLayout.ownerArea bits stride
  let incoming:=resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
  let pay:=cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
  let charges:=StripChart.charges F (v.sized (v.seed P h width) width) v.cost (E).stop
  chargedMasterWords E charges (v.emptyReserve P h width) (v.wideOrder h width) M
    (WideMemory.groups h v.W) (WideMemory.dir h v.W k v.wideJobs) (P).joint N v.depth
    (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) π (TerminalLayout.reserve start cnt bits)
    (rowOnly v.mesh decl (own.base v.mesh)) (rowOnly v.mesh decl pay) (routeBanks start cnt r)
    o PurchaseInventory.slot (fun j=>(pairKeys (Columns h D) k j).val)
    (sinkBank start cnt r (P).catalogue.rows) (P).catalogue.rows raw

def wideSignedChart (stock : Bank) :=
  let bits:=page stock
  v.nativeChart P h width r (TerminalLayout.settlement bits stock) (TerminalLayout.source bits)
    (TerminalLayout.table bits) (TerminalLayout.destination bits) (sinkBank start cnt r (P).catalogue.rows)

/-- Output of the authentic subdivision applied to the finite master input. -/
def wideSignedMidAt (size : ℕ) (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) :=
  Boot.booted (v.catalystMarkets P h width) size (v.wideSignedWords h width stock M π o raw)

/-- This is the same native pre-settlement checkout whose booked cash columns are
packed. The positive purchased-edge geometry is read directly from this memory. -/
def wideSignedCheckoutAt (size : ℕ) (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) :=
  checkedOut (v.wideSignedChart h width stock) ((A).endAddress v.mesh)
    (v.wideSignedMidAt h width size stock M π o raw)

/-- The smallest checkout is sufficient when all requested readback ends
at the physical calendar. -/
def wideSignedCheckout := v.wideSignedCheckoutAt h width ((A).endAddress v.mesh)

/-- The original hardware boot establishes the complete common source for economic
replay, row settlement and the funded reserve, at exactly the finite input extent
given to the signed continuation. -/
abbrev wide_signed_boot_at (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh<2^w) :=
  let pfx:=v.wideGeometryPrefix h width
  let bits:=page stock
  let owners:=sinkBank start cnt r (P).catalogue.rows
  let own:=TerminalLayout.ownerArea bits stride
  let market:=v.catalystMarkets P h width
  let charge:=StripChart.charges F (v.sized (v.seed P h width) width) v.cost (E).stop
  let empty:=v.emptyReserve P h width
  let freq:=DeadlineROM.prices v.mesh v.finish (v.basePhase width)
  let incoming:=resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
  let pay:=cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
  let Eord : (E).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh
    (P).joint (P).catalogue (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  let stop:=v.catalyst_static_end P h width A
  have below : owners.base+owners.size≤(A).endAddress v.mesh:=stop.le.trans (Nat.le_add_right ..)
  have static:=allocated_space start cnt r (P).catalogue.rows w (⟨0,bits+2⟩:Bank) (8*2^bits)
    (below.trans_lt room)
  master_start_all E Eord charge empty rfl rfl rfl (v.wideOrder h width) M (WideMemory.groups h v.W)
    (WideMemory.dir h v.W k v.wideJobs) (P).joint N v.depth freq π (TerminalLayout.reserve start cnt bits)
    (rowOnly v.mesh decl (own.base v.mesh)) (rowOnly v.mesh decl pay) (routeBanks start cnt r) o
    PurchaseInventory.slot (fun j=>(pairKeys (Columns h D) k j).val) owners (P).catalogue.rows raw market
    (v.catalyst_market_layout_at P h width size pfx.2.1 extent) (v.wideSources h width).2 static
    (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (v.reserve_before_catalystStaticStart P h width)
    (below.trans_lt room) (below.trans extent) (fun j=>stop.le.trans (v.catalyst_market_low P h width j))
    pfx.1 le_rfl pfx.2.1 pfx.2.2

/-- The unmodified tables, input permutation, purchased row directory and shared
role header at the actual memory presented to each attempted repair. -/
theorem wide_signed_dated_at (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh<2^w)
    (mounted : Calendar.mounted (v.wideSignedChart h width stock) (events v.mesh)
      (v.wideSignedMidAt h width size stock M π o raw)) (a : Attempt) :
    DatedBoard F s v.mesh (P).catalogue (P).routes π (WideMemory.groups h v.W)
      (WideMemory.dir h v.W k v.wideJobs) a
      (entryMemory (v.wideSignedChart h width stock) (v.wideSignedMidAt h width size stock M π o raw) a) := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  obtain ⟨_,_,seen,econ,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π o raw room
  let addr:=v.catalystPlacement_addresses h (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) (P).joint (P).catalogue (v.wideSources h width).2
  have ordered : (E).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh
    (P).joint (P).catalogue (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have economic : (E).stop≤(A).first:=(Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)
  apply datedBoard F s v.mesh (P).catalogue (P).routes π (WideMemory.groups h v.W)
    (WideMemory.dir h v.W k v.wideJobs) A (v.wideSignedChart h width stock) _ a
    (v.wideOrder h width) (v.wideSources h width).2 seen E ordered econ
    ((v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width))
    economic (first.trans_lt room) addr.1 addr.2.1 addr.2.2.1 addr.2.2.2.1
    (v.catalyst_header P h width a) mounted
  intro e x hx
  exact (v.event_prefix P h width r _ _ _ _ _ e x hx).1

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- All thirteen catalogue/calendar/owner placement operands are compiled from the one
fixed geometry, including the current signed role data and original terminal core rows. -/
abbrev wide_signed_run_at :=
  fun (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (slices : List PaidWidths.Slice)
    (stockEnd : stock.base+stock.size≤(A).endAddress v.mesh)
    (age : v.wideSignedHeight≤h) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) =>
    let pfx:=v.wideGeometryPrefix h width
    have full : max (max v.stripHeight ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)
        (max (max (fuel v.mesh) v.keepLimit) (Fintype.card (Actions (publicStages v.W) k)))≤h:=(le_max_left ..).trans age
    have late : v.stripHeight≤h:=(le_max_left ..).trans ((le_max_left ..).trans full)
    have threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h:=(le_max_right ..).trans ((le_max_left ..).trans full)
    have clock : max (max (fuel v.mesh) v.keepLimit) (Fintype.card (Actions (publicStages v.W) k))≤h :=
      (le_max_right ..).trans full
    let bits:=page stock
    let endBoard:=sinkBank start cnt r (P).catalogue.rows
    have fits:=v.wide_signed_room h width stock stockEnd age budget
    have room : 28*2^bits<2^w:=fits.1
    have address : (A).endAddress v.mesh<2^w:=fits.2
    have above : h<2^w:=(Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)
    have alph : v.menu.alphabet≤h:=by
      have one : v.menu.alphabet≤v.stripPorts (publicStages v.W)+v.menu.alphabet:=Nat.le_add_left ..
      have toHeight : v.stripPorts (publicStages v.W)+v.menu.alphabet≤v.stripHeight :=
        (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (le_max_left ..))
      exact one.trans (toHeight.trans late)
    have counter : v.menu.alphabet*width<2^w:=by
      calc
        _≤2^h*2^h:=Nat.mul_le_mul (alph.trans (Nat.lt_two_pow_self (n:=h)).le) small
        _=2^(h+h):=(pow_add ..).symm
        _<2^w:=Nat.pow_lt_pow_right (by decide) (by rw [Native.wordBits_linear];omega)
    let board:=fun a live=>(v.fixed_post h width r (WideMemory.K h v.W)
      (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
      (WideMemory.R v.sampler h v.W k) 0 (P).joint (v.wideSources h width).2
      (TerminalLayout.settlement bits stock) (TerminalLayout.source bits) (TerminalLayout.table bits)
      (TerminalLayout.destination bits) endBoard a live pfx.2.2 address (threshold.trans_lt above)
      (small.trans_lt (v.date_prefix_fit h)) (alph.trans above.le) counter).1
    let source:=v.wideSignedCheckoutAt h width size stock M π o raw
    let place:=siteNumber h D k
    let B:=(P).catalogue.coreMount π place (v.wideOrder h width) source
    let market:=v.catalystMarkets P h width
    let layout:=v.catalyst_market_layout_at P h width size pfx.2.1 extent
    let endAt:=v.catalyst_static_end P h width A
    let solve:=v.catalyst_run h width (P).joint (P).catalogue (v.wideOrder h width) M (WideMemory.groups h v.W)
      (WideMemory.dir h v.W k v.wideJobs) (v.wideSources h width).2 π place B stock slices o market raw layout
    fun state mounted paid =>
      solve (v.wide_geometry_at_page h width stock stride start num cnt room)
        room (endAt.le.trans ((Nat.le_add_right ..).trans extent))
        (fun j=>endAt.le.trans (v.catalyst_market_low P h width j)) pfx.1 pfx.2.1 pfx.2.2
        state (fun _=>rfl) mounted late small threshold clock (le_refl _) board paid

abbrev wide_signed_run := v.wide_signed_run_at h width ((A).endAddress v.mesh) le_rfl

/-- Settlement of the live stock bank left by the final feed, with the original
finite input extent maintained for the height-independent signed readback code. -/
abbrev wide_retained_run_at (size : ℕ) (extent : (A).endAddress v.mesh≤ size)
    (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (slices : List PaidWidths.Slice) :=
  v.wide_signed_run_at h width size extent (v.fixedTerminalStock P h width) M π (wideRouteOrder h D k)
    raw slices (v.fixedTerminalStock_end P h width)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
