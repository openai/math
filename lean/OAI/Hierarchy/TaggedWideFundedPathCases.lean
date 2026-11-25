import OAI.Hierarchy.TaggedWideFundedPathCutRows
import OAI.Hierarchy.WidthSignedPathCertificate

namespace OAI
/-! # Dependent transport from the signed native report on a complete path -/

universe uData

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "start" => v.wideOrigin h width size seed π
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (j : CalendarTape.Path (v.wideSelector h width age budget small).format.slot
    (events v.mesh) (v.wideOrigin h width size seed π))
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j


local notation "alignmentWords" => Fintype.card (Columns h (2^v.W)) * k
local notation "paidCost" => ∀ e : Fin (table).catalogue.rows,
  PaidWidths.total (v.widePaidSlices h width v.maxBits) checkout e +
    (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w
local notation "nameAlignment" => ∀ {n : ℕ} (owner : Fin n → Fin alignmentWords) (fees : Fin n → ℕ),
  v.WideFundedAlignment h width size v.maxBits π.symm raw owner fees
    (fun z => (CatalystArchive.pairKeys (Columns h (2^v.W)) k z).val)
local notation "ReportSpace" => (U : _) × CoreBoard.Report π (2^v.W) k width (fuel v.mesh*width) v.radius 1 U
local notation "pathValue" => (⟨_,pathReport⟩ : ReportSpace)
local notation "native" a:arg c:arg ns:arg => v.signedPathNativeReport h width size π.symm raw v.maxBits expanse a budget small c (0 : Word w) ns
local notation "nrows" => (v.widePlacement h width).catalogue.rows
local notation "RowSpace" => (lines : Fin nrows → ProtocolRAMEmit.Row) ×
  ProtocolRAMEmit.Geometry (boardLayout h (2^v.W) k width (fuel v.mesh*width)) v.radius 1 lines
local notation "tableOf" r:arg => (⟨(r).rows,(r).geometry⟩ : RowSpace)

/-- All fields of the original signed terminal report survive the two changes
of ledger proof, including the mount, enumeration, receipt and paid widths. -/
theorem wide_reported_path_native :
    ∃ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      pathValue=⟨_,(native admitted cost names)⟩ := by
  exact v.wide_reported_path_signed_packed h width size π seed age budget small expanse late room j

/-- Transport an arbitrary proof or value indexed by the complete report at
the physical widths selected by this path. -/
def wide_funded_path_cases (Y : ReportSpace → Sort uData)
    (atNative : ∀ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 →
      Y ⟨_,(native admitted cost names)⟩) : Y pathValue := by
  apply Classical.choice
  obtain ⟨admitted,cost,names,accept,eqn⟩ :=
    v.wide_reported_path_native h width size π seed age budget small expanse late room j
  exact ⟨eqn.symm ▸ atNative admitted cost names accept⟩

/-- Transport both the full physical report and the actual fixed-chart receipt
when a local execution or its output refers to data from both. -/
def wide_funded_path_report_cases (unitCost : ℕ)
    (Y : ReportSpace → (s : RowSpace) →
      v.FundedCutRows h width size π.symm raw s.1 s.2 unitCost → Sort uData)
    (atNative : ∀ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 →
      let r:=native admitted cost names
      let board:=tableOf r
      (a : v.FundedCutRows h width size π.symm raw board.1 board.2 unitCost) → Y ⟨_,r⟩ board a)
    (actual : v.FundedCutRows h width size π.symm raw (pathReport).rows (pathReport).geometry unitCost) :
    Y pathValue (tableOf pathReport) actual := by
  apply Classical.choice
  obtain ⟨admitted,cost,names,accept,whole⟩ :=
    v.wide_reported_path_native h width size π seed age budget small expanse late room j
  let r:=native admitted cost names
  let board:=tableOf r
  have geometry := congrArg (fun a : ReportSpace => reportGeometry π a.2) whole
  have eqBoard : (tableOf pathReport) = board := eq_of_heq (Sigma.mk.inj_iff.mp geometry).2
  have both : (pathValue,tableOf pathReport)=((⟨_,r⟩ : ReportSpace),board) := Prod.ext whole eqBoard
  let useAt (a : ReportSpace × RowSpace) :=
    (pay : v.FundedCutRows h width size π.symm raw a.2.1 a.2.2 unitCost) → Y a.1 a.2 pay
  have one : useAt ((⟨_,r⟩ : ReportSpace),board) := atNative admitted cost names accept
  have result : useAt (pathValue,tableOf pathReport) := both.symm ▸ one
  exact ⟨result actual⟩

/-- In the fixed physical edge chart the motive can depend on the actual
funding certificate and every field of its source alignment. -/
def wide_funded_path_cut_cases (unitCost : ℕ)
    (Y : (s : RowSpace) → v.FundedCutRows h width size π.symm raw s.1 s.2 unitCost → Sort uData)
    (atNative : ∀ (admitted : v.wideFundedHeight≤h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 →
      let board:=tableOf (native admitted cost names)
      (a : v.FundedCutRows h width size π.symm raw board.1 board.2 unitCost) → Y board a)
    (actual : v.FundedCutRows h width size π.symm raw (pathReport).rows (pathReport).geometry unitCost) :
    Y (tableOf pathReport) actual := by
  exact v.wide_funded_path_report_cases h width size π seed age budget small expanse late room j
    unitCost (fun _ s a=>Y s a) atNative actual

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
