import OAI.Hierarchy.ProbeFixedFundedWidth
import OAI.Hierarchy.ProbeFixedBroadcastCap

namespace OAI
/-! # Exact original normalized widths after the funded native reporter -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets PurchaseFrozen
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

set_option cleanup.letToHave false
set_option maxRecDepth 8192
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

set_option maxHeartbeats 2000000 in
private abbrev WideFundedWidthStatement : Prop :=
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width (small : width ≤ 2^h) (_ : v.widthFloor ≤ width)
      (budget : v.keepLimit*width+1 ≤ 2^h),
      v.paidWordFactor v.maxBits*width≤2^h →
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (size : ℕ)
        (extent : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
        (state : Word (Native.wordBits h (2^v.W) Native.copies)),
      let P := v.widePlacement h width
      let G := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let r := Fintype.card (Slots h (2^v.W) k)
      let page := v.wideSignedPage h width stock
      let f := v.nativeBoards P h width
      let cnt := rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger f v.mesh P.catalogue P.routes F G))
      let owners := sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
      let banks := TerminalLayout.settlement page stock
      let src := TerminalLayout.source page
      let tab := TerminalLayout.table page
      let dst := TerminalLayout.destination page
      let tape := v.wideFundedRaw h width v.maxBits raw
      let order := wideRouteOrder h (2^v.W) k
      let m := v.wideSignedMidAt h width size stock v.radius π order tape
      let checks := v.wideSignedCheckoutAt h width size stock v.radius π order tape
      let out := run (v.wideSignedChart h width stock) (events v.mesh) m
      let marks := v.birthMarks P h width r banks src tab dst owners m
      let ord := P.catalogue.ordinal v.sampler π v.depth marks (v.wideOrder h width) rfl
      let _len := lenCode v.sampler π v.depth marks v.radius
      let paid := Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent age budget small state)
      checks (G.endAddress v.mesh)=0 →
      (∀i : Fin P.catalogue.rows,PaidWidths.total (v.widePaidSlices h width v.maxBits) checks i=
        PaidWidths.total (v.widePaidSlices h width v.maxBits) out i) →
      ∀e, ((Whole.Reconciliation.originalWidth
        (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k)
        paid.1 (ord e) : ℕ) : ℝ)/width =
        v.fundedProfile h width π m v.maxBits (Whole.Reconciliation.usedAt
          (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k)
          paid.1) e

set_option maxHeartbeats 4000000 in
theorem wide_funded_width_of_paid : WideFundedWidthStatement v := by
  refine ((v.wide_paid_total_bill v.maxBits).and
    (Filter.eventually_ge_atTop (v.overflowFactor v.keepLimit+fuel v.mesh))).mono ?_
  intro h conditions
  obtain ⟨spend,late⟩ := conditions
  intro width small floor budget capacity π raw size extent age state P G stock r page f cnt owners banks src tab dst tape
    order m checks out marks ord len paid accepted equal e
  have granted := (v.wide_funded_extent h width v.maxBits).trans extent
  have charge := spend width small floor budget capacity size granted π tape accepted
  have word := v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget
  have physical := v.wide_funded_stock_at_size h width v.radius π raw v.maxBits size extent age budget small
  have mounted := v.wide_funded_paid_at_size h width v.radius π raw v.maxBits size extent age budget small
  have residual : (v.overflowFactor v.keepLimit+fuel v.mesh)*width ≤ 2^h*2^h :=
    Nat.mul_le_mul (late.trans (Nat.lt_two_pow_self (n:=h)).le) small
  have cost (i : Fin P.catalogue.rows) :
      PaidWidths.total (v.widePaidSlices h width v.maxBits) checks i +
        (v.overflowFactor v.keepLimit+fuel v.mesh)*width <
          2^(Native.wordBits h (2^v.W) Native.copies) := by
    calc
      _ ≤ 2^h*2^h+2^h*2^h := Nat.add_le_add (charge i) residual
      _ = 2^(h+h+1) := by rw [pow_succ,pow_add]; omega
      _ < 2^(Native.wordBits h (2^v.W) Native.copies) :=
        Nat.pow_lt_pow_right (by decide) (by rw [Native.wordBits_linear]; omega)
  let receipt := paid.1
  have result := v.funded_width_at h width size v.radius π tape v.maxBits
    _ _ _ physical mounted word.1 cost equal receipt e
  exact result

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
