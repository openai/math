import OAI.Hierarchy.ProbeFixedWideAttemptInvoice
import OAI.Hierarchy.ProbeFixedWideForest
import OAI.Hierarchy.ProbeFixedFundedBudget

namespace OAI
/-! # The terminal width budget for every accepted word on the funded native calendar -/
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
private abbrev FundedBudgetStatement : Prop :=
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width (small : width ≤ 2^h) (_ : v.widthFloor ≤ width)
      (budget : v.keepLimit*width+1 ≤ 2^h),
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
      let _out := run (v.wideSignedChart h width stock) (events v.mesh) m
      let marks := v.birthMarks P h width r banks src tab dst owners m
      let _ord := P.catalogue.ordinal v.sampler π v.depth marks (v.wideOrder h width) rfl
      let len := lenCode v.sampler π v.depth marks v.radius
      let paid := Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent age budget small state)
      checks (G.endAddress v.mesh)=0 →
      TermBudget p q Q Λ (2^h) width v.radius (∑_j : Columns h (2^v.W)×Fin k,fuel v.mesh*width)
        (scaleOf v.sampler π v.depth marks) (fun e => (len e:ℝ))
        (v.fundedProfile h width π m v.maxBits (Whole.Reconciliation.usedAt (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k)
            (J := Columns h (2^v.W) × Fin k) paid.1))

set_option maxHeartbeats 4000000 in
theorem funded_budget : FundedBudgetStatement v := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  refine (v.funded_budget_of_invoices.and
    (v.wide_attempt_invoice.and (v.wide_forest_invoice.and v.wide_feed_invoice))).mono ?_
  intro h hs
  obtain ⟨bill, attempts, forests, feeds⟩ := hs
  intro width small floor budget π raw size extent age state P G stock r page f cnt owners banks src tab dst tape
    order m checks out marks ord len paid accepted
  have outerBound := (v.wide_funded_extent h width v.maxBits).trans extent
  have billed := bill width small floor budget π raw v.maxBits size extent age state accepted
  have attemptCharge := attempts width small budget size outerBound π tape
  have forestCharge := forests width small budget size outerBound π tape
  have feedCharge := feeds width small budget size outerBound π tape
  have result := billed (by
    intro event live
    cases event with
    | attempt a => exact attemptCharge a live (forestCharge a live)
    | feed b => exact feedCharge b v.maxBits)
  exact result

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
