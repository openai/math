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

theorem preclip_strict (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (large : v.wideSpillSheetHeight≤h)
    (archived : ∀n<(A).endAddress v.mesh,input J.index n=archive n) :
    J.preclipCapFit expanse height.measure first input (fun _=>view unitCost) ∧
    (∀ch, installedWidths (directions ∘ names) (datedValue J.index.val ∘ address ∘ names) ch<room unitCost) ∧
    (∀ch, installedWidths (directions ∘ names) (correctedWidths 0 J.index.succ ∘ address ∘ names) ch<room unitCost) := by
  let boundExtent := (v.wide_funded_extent h width v.maxBits).trans expanse
  let caps := max_le_iff.mp (max_le_iff.mp height.report).1
  let pathTape := v.wideFundedRaw h width v.maxBits (rawOf J)
  have accepted := (v.wide_verdict h width size boundExtent v.radius π.symm pathTape age budget small).mpr J.valid
  have original := height.funded_aperture size unitCost expanse rate π.symm pathTape accepted
  have regular (q : Fin ((es).length+1)) i :
      (datedValue q.val ∘ address ∘ names) i ≤ view unitCost :=
    (original terms q.val (Nat.le_of_lt_succ q.isLt) i false).trans
      (HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (fuel v.mesh) width _)
  have spillAge : v.wideSpillOverflowHeight ≤ h := (max_le_iff.mp (max_le_iff.mp large).2).2
  have sizeWord := (v.purchased_table_room h (v.wide_stock_sizes h width age budget small).strip).2.2.2
  have uncut := v.wide_spill_preclip_rows h width v.maxBits size v.radius π.symm (rawOf J)
    first J.index (input J.index) unitCost rate spillAge boundExtent height.floor small budget sizeWord
    rfl accepted archived marked terms expanse caps.1 (regular J.index.succ)
  have fit (i) : (correctedWidths 0 J.index.succ ∘ address ∘ names) i ≤ view unitCost := by
    simp only [wideCorrectedWidths, Fin.cases_succ, ite_true]
    exact uncut i
  exact ⟨fun i _=>fit i,
    v.wide_neighbor_chord_lt h width unitCost π.symm marked J.preclipUnique names _
      (regular J.index.castSucc),
    v.wide_neighbor_chord_lt h width unitCost π.symm marked J.preclipUnique names _ fit⟩

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
