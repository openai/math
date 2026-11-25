import OAI.Hierarchy.TaggedWireReportedPath
import OAI.Hierarchy.TaggedWideCursorReportRows
import OAI.Hierarchy.WidthSignedPathCertificate

namespace OAI
/-! # Identifying each calendar branch with the original funded terminal row geometry -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option cleanup.letToHave false
set_option Elab.async false
attribute [local irreducible] Nat.pow

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
variable (j : Path slots es start)
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "alignmentWords" => Fintype.card (Columns h (2^v.W)) * k
local notation "paidCost" => ∀ e : Fin (table).catalogue.rows,
  PaidWidths.total (v.widePaidSlices h width v.maxBits) checkout e +
    (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w
local notation "nameAlignment" => ∀ {n : ℕ} (owner : Fin n → Fin alignmentWords) (fees : Fin n → ℕ),
  v.WideFundedAlignment h width size v.maxBits π.symm raw owner fees
    (fun z => (CatalystArchive.pairKeys (Columns h (2^v.W)) k z).val)
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j

local notation "fundedNative" a:arg c:arg ns:arg =>
  v.signedPathNativeReport h width size π.symm raw v.maxBits expanse a budget small c (0 : Word w) ns

/-- The original authenticated checkout, its exact selector tape, and its full
dependent geometry are available for the report delivered by this very path. -/
theorem wide_reported_path_funded :
    ∃ (admitted : v.wideFundedHeight ≤ h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      reportGeometry π pathReport=reportGeometry π
        (fundedNative admitted cost names) := by
  exact v.wide_reported_path_signed_geometry h width size π seed age budget small expanse late room j

/-- The projection used by the positive and private ranked gates. It keeps the
original ordinal row table at the width-independent layout boundary. -/
theorem wide_reported_path_funded_rows :
    ∃ (admitted : v.wideFundedHeight ≤ h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      let native:=fundedNative admitted cost names
      (⟨(pathReport).edges,(pathReport).rows⟩ : (n:ℕ) × (Fin n → ProtocolRAMEmit.Row))=
        ⟨native.edges,native.rows⟩ := by
  have witnessed := v.wide_reported_path_funded h width size π seed age budget small expanse late room j
  rcases witnessed with ⟨a,c,n,accept,eqn⟩
  refine ⟨a,c,n,accept,?_⟩
  exact congrArg (fun d : RowGeometry h (2^v.W) k width (fuel v.mesh*width) v.radius 1 =>
    (⟨d.1,d.2.1⟩ : (n:ℕ) × (Fin n → ProtocolRAMEmit.Row))) eqn

private theorem packed_rows_and_keep {hh dd kk ww allowance radius denominator : ℕ}
    {perm : Equiv.Perm (Tagged.Row hh)}
    {left right : (U : _) × CoreBoard.Report perm dd kk ww allowance radius denominator U}
    (same : left = right) :
    (⟨left.2.edges, left.2.rows⟩ : (n : ℕ) × (Fin n → ProtocolRAMEmit.Row)) =
      ⟨right.2.edges, right.2.rows⟩ ∧
      (left.2.geometry.links.Keep (2^hh) ↔ right.2.geometry.links.Keep (2^hh)) := by
  cases same
  exact ⟨rfl, Iff.rfl⟩

/-- The complete path and its native report give identical routed chords,
including scale data. Both equalities use one signed checkout and row ranking. -/
theorem wide_reported_path_funded_keep :
    ∃ (admitted : v.wideFundedHeight ≤ h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      let native:=fundedNative admitted cost names
      (⟨(pathReport).edges,(pathReport).rows⟩ : (n:ℕ) × (Fin n → ProtocolRAMEmit.Row))=
        ⟨native.edges,native.rows⟩ ∧
      ((pathReport).geometry.links.Keep (2^h) ↔ native.geometry.links.Keep (2^h)) := by
  have witnessed := v.wide_reported_path_signed_packed h width size π seed age budget small expanse late room j
  rcases witnessed with ⟨admitted, cost, names, accepted, same⟩
  exact ⟨admitted, cost, names, accepted, packed_rows_and_keep same⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
