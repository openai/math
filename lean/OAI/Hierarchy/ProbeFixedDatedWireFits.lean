import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.TaggedWideDatedRows
import OAI.Hierarchy.ProbeFixedSharpPaidRows
import OAI.Hierarchy.TaggedWireArchiveAperture

namespace OAI
/-! # Every chronological bit fits its named physical aperture -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
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
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tbl" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r rows
local notation "C" => v.wideSignedChart h width stock
local notation "bs" => v.stockBanks P h width
local notation "es" => events v.mesh
local notation "compile" => v.wideEventSlices h width v.maxBits
local notation "axis" => pairKeys (Columns h D) k
local notation "cardFit" => (rfl : v.wideJobs*(PurchaseFrozen.count h D k*PurchaseFrozen.paths h v.sampler.degree v.depth)=(P).catalogue.boughtRows)
local notation "catalog" => fun π days=>(P).catalogue.ordinal v.sampler π v.depth days order cardFit
local notation "embed" => fun π days=>DatedRows.embed v.sampler π v.depth days (P).catalogue order cardFit
local notation "names" => fun π days=>timeRows v.sampler π v.depth days (P).catalogue order cardFit axis

/-- Every sparse chronological source has the same aperture on its two
physical incidences, including when only one end of a purchased link is read. -/
def DatedWireFits (π : Equiv.Perm (Fin (2^h))) (initial archive : Memory w) (unitCost : ℕ) : Prop :=
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let days:=v.birthMarks P h width r old src tbl dst owners initial
  let ex:=v.paid_days_exclusive h width r old src tbl dst owners initial
  ∀issues : Attempt→Entry num width,∀j≤(es).length,∀i side,
    (v.wideDatedValue h width v.maxBits initial archive issues j ∘ embed π days ∘ names π days) i≤
      HistoryRoles.ceiling v.sampler v.mesh unitCost v.keepLimit (fuel v.mesh) width
        (named v.sampler π v.depth days ex (names π days) (i,side))

set_option maxHeartbeats 1800000 in
theorem dated_wire_fits_of_prices (π : Equiv.Perm (Fin (2^h))) (initial archive : Memory w)
    (unitCost : ℕ) (bounded : StockBound.Run C bs initial h N k (v.keepLimit*width))
    (paid : ∀t∈es,∀e : Fin rows,PaidWidths.total (compile t) archive e≤unitCost*width) :
    v.DatedWireFits h width π initial archive unitCost := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  intro issues j last i side
  let days:=v.birthMarks P h width r old src tbl dst owners initial
  let ex:=v.paid_days_exclusive h width r old src tbl dst owners initial
  let ev:=(es)[j]?
  let memory:=StockBound.state C initial j
  let active : HistoryRoles.Goods h v.W k → ℕ := PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) memory
  let saved : HistoryRoles.Goods h v.W k → ℕ := PurchaseInventory.stock (DatedGoods.stash bs ev) memory
  let used:=fun a=>PrefixReserve.used (CatalystArchive.site v.mesh issues) (CatalystArchive.debit v.mesh issues) (PrefixReserve.countAt v.mesh issues j) (axis a)
  let price:=fun t (hit:t∈es) e=>paid t hit (catalog π days e)
  let fit:=HistoryRoles.fits v.sampler π v.depth days ex v.mesh compile archive (catalog π days) unitCost v.keepLimit
    (fuel v.mesh) width (names π days) j (DatedGoods.phase v.mesh ev) (DatedGoods.releases ev)
    (DatedGoods.bought (C).modeAt ev memory) active saved used price
    (v.prefix_active_bound P h width r old src tbl dst owners initial j last bounded)
    (v.prefix_stash_bound P h width r old src tbl dst owners initial j last bounded)
  let values:=v.wideDatedValue h width v.maxBits initial archive issues j
  have table : values ∘ embed π days=HistoryRoles.amount v.sampler π v.depth days
      (HistoryRoles.archive v.sampler π v.depth days v.mesh compile archive (catalog π days) j)
      (HistoryRoles.live v.mesh width (DatedGoods.phase v.mesh ev) (DatedGoods.releases ev) active saved
        (DatedGoods.bought (C).modeAt ev memory)) (HistoryRoles.remaining (fuel v.mesh) width used) := by
    funext chord
    rcases chord with e|i|a <;> rfl
  change (values ∘ embed π days) ((names π days) i)≤_
  rw [table]
  exact fit i side

/-- All heights past this same threshold work uniformly for every admissible
width, completed tape, date, original row, side and reserve debit history. -/
theorem wide_dated_wire_fits :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.widthFloor≤width→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let original:=v.fixedTerminalStock placed h width
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let mid:=v.wideSignedMidAt h width size original v.radius π o raw
      let check:=v.wideSignedCheckoutAt h width size original v.radius π o raw
      check ((arena).endAddress v.mesh)=0→∀unitCost,v.sharpPaidUnit≤unitCost→v.DatedWireFits h width π mid check unitCost := by
  filter_upwards [v.wide_sharp_paid_rows,Filter.eventually_ge_atTop v.wideStockHeight] with h price age
  intro width small floor budget placed arena original size extent π raw o mid check ok unitCost enough
  let booked:=(price width small floor budget size extent π raw ok)
  exact v.dated_wire_fits_of_prices h width π mid check unitCost
    (v.wide_stock_at h width size extent v.radius π raw age budget small)
    (fun t ht e=>(booked t ht e).trans (Nat.mul_le_mul_right width enough))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
