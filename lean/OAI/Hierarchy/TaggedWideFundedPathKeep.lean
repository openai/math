import OAI.Hierarchy.TaggedWideFundedCursorRows
import OAI.Hierarchy.TaggedWireActiveRouting

namespace OAI
/-! # The keep test on a routed ordinal is the keep test on its actual signed report -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute CatalystArchive
open WireTelescope Tagged CalendarTape CoreBoard.PhysicalTerm
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192

private theorem keep_on_equal_geometry {h d k w R M den : ℕ}
    {a b : RowGeometry h d k w R M den} (eqn : a = b) :
    a.2.2.links.Keep (2^h) ↔ b.2.2.links.Keep (2^h) := by
  cases eqn
  rfl

private theorem retained_report_fields {h d k w R M den : ℕ}
    {F X : Type} [Field F] {slot : Event → CalendarTape.Slot X} {events : List Event}
    {base : Equiv.Perm (Tagged.Row h) → X} (Z : CalendarTerms F h d k w R M den slot events base)
    (S : Type) [Fintype S] (π : Equiv.Perm (Tagged.Row h)) (i : Fin ((Z.nativeRouting S).count π))
    {U} (native : CoreBoard.Report π d k w R M den U)
    (same : reportGeometry π (Z.reported π ((Fintype.equivFin (Path slot events (base π))).symm i)) =
      reportGeometry π native) :
    let source := Z.reported π ((Fintype.equivFin (Path slot events (base π))).symm i)
    (⟨source.edges,source.rows⟩ : (n : ℕ) × (Fin n → ProtocolRAMEmit.Row)) = ⟨native.edges,native.rows⟩ ∧
      (((Z.nativeRouting S).links ⟨π,i⟩).Keep (2^h) ↔ native.geometry.links.Keep (2^h)) := by
  constructor
  · exact congrArg (fun b : RowGeometry h d k w R M den =>
      (⟨b.1,b.2.1⟩ : (n : ℕ) × (Fin n → ProtocolRAMEmit.Row))) same
  · let chosen := (Fintype.equivFin (Path slot events (base π))).symm i
    let source := Z.reported π chosen
    have equal : reportGeometry π source = reportGeometry π native := same
    have keep := keep_on_equal_geometry (a:=reportGeometry π source) (b:=reportGeometry π native) equal
    have left := congrArg (fun L : TaggedPrune.Links (boardLayout h d k w R) M => L.Keep (2^h))
      (Z.retained_links S π i)
    exact (Iff.of_eq left).trans keep


variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (word : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "state" => v.wideOrigin h width size seed
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (Z : CalendarTerms F h (2^v.W) k width (fuel v.mesh*width) v.radius 1 slots es state)
    (S : Type) [Fintype S] (i : Fin ((Z.nativeRouting S).count π))
local notation "j" => (Fintype.equivFin (Path slots es (state π))).symm i
local notation "raw" => (reader).format.windows.header es (encode slots es (state π) j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late word j
local notation "alignmentWords" => Fintype.card (Columns h (2^v.W)) * k
local notation "paidCost" => ∀ e : Fin (table).catalogue.rows,
  PaidWidths.total (v.widePaidSlices h width v.maxBits) checkout e +
    (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w
local notation "nameAlignment" => ∀ {n : ℕ} (owner : Fin n → Fin alignmentWords) (fees : Fin n → ℕ),
  v.WideFundedAlignment h width size v.maxBits π.symm raw owner fees
    (fun z => (CatalystArchive.pairKeys (Columns h (2^v.W)) k z).val)

local notation "rowsAndGeometry" => RowGeometry h (2^v.W) k width (fuel v.mesh*width) v.radius 1

/-- The geometry argument is reflexivity for the elected calendar. The row
equality, native decision, and original physical acceptance share the same witnesses. -/
theorem wide_routing_funded_keep
    (same : reportGeometry π (Z.reported π j)=reportGeometry π pathReport) :
    ∃ (admitted : v.wideFundedHeight ≤ h) (cost : paidCost) (names : nameAlignment),checkout ceiling=0 ∧
      let native:=v.signedPathNativeReport h width size π.symm raw v.maxBits expanse admitted budget small
        cost (0:Word w) names
      (⟨(Z.reported π j).edges,(Z.reported π j).rows⟩ : (n:ℕ) × (Fin n → ProtocolRAMEmit.Row))=
        ⟨native.edges,native.rows⟩ ∧
      (((Z.nativeRouting S).links ⟨π,i⟩).Keep (2^h) ↔ native.geometry.links.Keep (2^h)) := by
  have witnesses := v.wide_reported_path_funded h width size π seed age budget small expanse late word j
  obtain ⟨a,c,n,accept,eqn⟩ := witnesses
  exact ⟨a,c,n,accept,retained_report_fields Z S π i _ (same.trans eqn)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
