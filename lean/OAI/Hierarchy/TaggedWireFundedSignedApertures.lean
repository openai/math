import OAI.Hierarchy.TaggedWireFundedPreclipStrict
import OAI.Hierarchy.TaggedWideSpillFieldRoom
import OAI.Hierarchy.TaggedWideDateApertures
import OAI.Hierarchy.TaggedWireFundedPreclipWidth
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.ProbeFixedWideSpillFieldRoom

namespace OAI
/-! # Row and chord bounds on the funded date's original preclip page -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 450000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "order" => wideRouteOrder h D k

variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
open Filter CalendarTape RepairHistogram HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
local notation "rawOf" J:arg => (L).header es (FundedDate.code J) seed
open private preclipEntriesAt from OAI.Hierarchy.TaggedWireFundedPreclipWidth

open HistoryRoles
variable (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (height : v.BranchRoleHeight h width)
    (first : ℕ) (input : Fin (es).length→Memory w)
local notation "cc" => (P).catalogue
local notation "nativeJ" => origin J.code
local notation "archive" => checkedOut C ((A).endAddress v.mesh) nativeJ
local notation "terms" => preclipEntriesAt (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (rawOf J) expanse height.measure small budget (0 : Word w)
local notation "marked" => v.birthMarks P h width r banks source table target owners nativeJ
local notation "nativeOrder" => v.wideOrder h width
local notation "cardRows" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π.symm v.depth marked cc nativeOrder cardRows axis
local notation "address" => DatedRows.embed v.sampler π.symm v.depth marked cc nativeOrder cardRows
local notation "directions" => HistoryRoles.sorted v.sampler π.symm v.depth marked
local notation "correctedWidths" => v.wideCorrectedWidths h width size v.radius π.symm (rawOf J) v.maxBits terms first input
local notation "clip" => fun i=>RouteSettlement.actual (v.wideSpillPage h width v.maxBits first J.index.val).overflow
  (input J.index) (PurchaseInventory.slot i)


local notation "datedValue" => v.wideDatedValue h width v.maxBits nativeJ archive terms
local notation "view" u:arg => v.wideHistoryUnit u*width
local notation "room" u:arg => v.wideNeighborCap width u

open WireTelescope NamedAperture Tagged PassiveWindow
local notation "K" => siteLast h D k+1
local notation "ends" => directions ∘ names
local notation "ports" => named v.sampler π.symm v.depth marked J.preclipUnique names
local notation "socket" => shelfSlot (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler π.symm v.depth marked J.preclipUnique names
local notation "pre" => datedValue J.index.val ∘ address ∘ names
local notation "middle" => correctedWidths 0 J.index.succ ∘ address ∘ names

local notation "sparse" => sparseKey v.sampler π.symm v.depth marked cc nativeOrder cardRows
  (PurchaseInventory.slotEquiv h (Stages h D) k) axis
theorem signedIdentifiers (native : ℕ) (physical : v.widePacketPhysical h width<2^native) :
    StrictMono (fun i=>((sparse) ((names) i)).val) ∧ (∀i,((sparse) ((names) i)).val<2^native) := by
  refine ⟨fun i j h'=>(time_before v.sampler π.symm v.depth marked cc nativeOrder cardRows axis i j).mp h',?_⟩
  intro i
  have row:=((sparse) ((names) i)).isLt
  have size:=v.wide_old_rows h width
  change Fintype.card (RoleProgram.Old h v.W k (P).catalogue.rows)<2^native at physical
  omega

private theorem row_le_chord {n sites : ℕ} (chords : Fin n→Chord sites) (lengths : Fin n→ℕ) (i : Fin n) :
    lengths i ≤ installedWidths chords lengths (chords i) := by
  by_cases live:0<lengths i
  · exact (Nat.le_add_left ..).trans (datedBase_room chords lengths i live)
  · have zero:lengths i=0:=by omega
    rw [zero]
    exact Nat.zero_le _

theorem signedRowBounds (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (large : v.wideSpillSheetHeight≤h) (archived : ∀n<(A).endAddress v.mesh,input J.index n=archive n) :
    (∀i,(pre) i≤room unitCost) ∧ (∀i,(middle) i≤room unitCost) := by
  have hit:=J.preclip_strict expanse height first input unitCost rate large archived
  exact ⟨fun i=>(row_le_chord ends pre i).trans (hit.2.1 _).le,
    fun i=>(row_le_chord ends middle i).trans (hit.2.2 _).le⟩

/-- The selected chronological source word on every incident role. Its slot
is the actual original role at this party, including parallel chords. -/
def signedInputParts (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (large : v.wideSpillSheetHeight≤h) (archived : ∀n<(A).endAddress v.mesh,input J.index n=archive n)
    (site : Fin K) (active : Widths K) (shape : installedWidths ends pre=active) :=
  let bound:=(J.preclip_strict expanse height first input unitCost rate large archived).2.1
  carried ends pre site (cap:=room unitCost) (fun i=>(row_le_chord ends pre i).trans (bound _).le)
    (PacketNeighbor.localSlot ends pre ports socket here site) shape

/-- The signed offer is measured before clipping, on the successor dated
role sheet with sector zero. -/
def signedOfferParts (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (large : v.wideSpillSheetHeight≤h) (archived : ∀n<(A).endAddress v.mesh,input J.index n=archive n)
    (site : Fin K) (active : Widths K) (shape : installedWidths ends middle=active) :=
  let bound:=(J.preclip_strict expanse height first input unitCost rate large archived).2.2
  carried ends middle site (cap:=room unitCost) (fun i=>(row_le_chord ends middle i).trans (bound _).le)
    (PacketNeighbor.localSlot ends middle ports socket here site) shape

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
