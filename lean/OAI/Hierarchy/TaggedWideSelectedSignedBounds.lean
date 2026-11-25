import OAI.Hierarchy.TaggedWireFundedSignedApertures
import OAI.Hierarchy.TaggedWideSelectedPreclipArchive
import OAI.Hierarchy.TaggedWideIndexedCursor
import OAI.Hierarchy.TaggedWideChordAperture

namespace OAI
/-! # Strict native aperture room for the input and preclip sides of a signed vote -/
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

theorem signed_parts_room (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (large : v.wideSpillSheetHeight≤h) (archived : ∀n<(A).endAddress v.mesh,input J.index n=archive n)
    (siteIndex : Fin K) (U V : Widths K) (inputWidth : installedWidths ends pre=U)
    (offerWidth : installedWidths ends middle=V) :
    let l:=J.signedInputParts expanse height first input unitCost rate large archived siteIndex U inputWidth
    let offered:=J.signedOfferParts expanse height first input unitCost rate large archived siteIndex V offerWidth
    (∀p:(portGraph K).Port siteIndex,U p.val.1≤room unitCost) ∧ (∀q,V q≤room unitCost) ∧
    (∀i,ChordAperture.room l i<room unitCost) ∧ (∀i,ChordAperture.room offered i<room unitCost) := by
  intro l offered
  have strict:=J.preclip_strict expanse height first input unitCost rate large archived
  have ul (q):U q<room unitCost:=by
    rw [←inputWidth]
    exact strict.2.1 q
  have vr (q):V q<room unitCost:=by
    rw [←offerWidth]
    exact strict.2.2 q
  have pos : 0<room unitCost:=Nat.two_pow_pos _
  refine ⟨fun p=>(ul p.val.1).le,fun q=>(vr q).le,?_,?_⟩
  · intro i
    unfold ChordAperture.room
    cases l.owner i with
    | none => exact pos
    | some p => exact ul p.val.1
  · intro i
    unfold ChordAperture.room
    cases offered.owner i with
    | none => exact pos
    | some p => exact vr p.val.1

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 650000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : TaggedPrune.OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future

local notation "inputs" => v.selectedPreclipInputs m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "archived" => v.selectedPreclipArchived m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate


abbrev selected_signed_bounds := (date).signed_parts_room Sfit height first inputs unitCost rate
  support.size.spillAge archived

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
